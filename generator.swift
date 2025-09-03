import Foundation

// === SplitMix64 PRNG ===
private struct SplitMix64 {
    private var state: UInt64
    init(seed: UInt64) { self.state = seed }
    mutating func next() -> UInt64 {
        state &+= 0x9E3779B97F4A7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58476D1CE4E5B9
        z = (z ^ (z >> 27)) &* 0x94D049BB133111EB
        return z ^ (z >> 31)
    }
    mutating func nextInt(in range: ClosedRange<Int>) -> Int {
        let span = UInt64(range.upperBound - range.lowerBound + 1)
        return range.lowerBound + Int(next() % span)
    }
    mutating func nextBool(probabilityTrue: Int = 50) -> Bool {
        precondition((0...100).contains(probabilityTrue))
        return nextInt(in: 0...99) < probabilityTrue
    }
}

private func fnv1a64(_ s: String) -> UInt64 {
    let offset: UInt64 = 1469598103934665603
    let prime:  UInt64 = 1099511628211
    var h = offset
    for b in s.utf8 { h ^= UInt64(b); h &*= prime }
    return h
}

// MARK: - Name Factory (паттерн имен)

public struct NameFactory {
    public init(module: String, parent: String, template: String, counter: Int) {
        self.module = module
        self.parent = parent
        self.template = template
        self.counter = counter
    }
    let module: String
    let parent: String
    let template: String
    private var counter: Int = 0
    mutating func make(_ base: String) -> String {
        counter += 1
        return "\(base)_\(module)\(parent)\(template)_\(counter)"
    }
}

private struct VarPools {
    let ints: [String]
    let strings: [String]
    let arr: String
    let dict: String
}

// MARK: - Язык инструкций

private enum Instruction {
    // числа (базовые + новые)
    case setInt(name: String, value: Int)
    case add(lhs: String, rhs: String, out: String)
    case sub(lhs: String, rhs: String, out: String)
    case mul(lhs: String, rhs: String, out: String)
    case divNZ(lhs: String, rhs: String, out: String)
    case modNZ(lhs: String, rhs: String, out: String)
    case absVar(name: String)
    case negate(name: String)
    case incByConst(name: String, delta: Int)
    case minAssign(out: String, a: String, b: String)
    case maxAssign(out: String, a: String, b: String)
    case clamp(name: String, minVar: String, maxVar: String)

    case bitAnd(lhs: String, rhs: String, out: String)
    case bitOr(lhs: String, rhs: String, out: String)
    case bitXor(lhs: String, rhs: String, out: String)
    case bitNot(name: String)
    case shiftLeft(name: String, byVar: String)
    case shiftRight(name: String, byVar: String)
    case rotl(lhs: String, by: String, out: String)          // NEW: rotate left
    case rotr(lhs: String, by: String, out: String)          // NEW: rotate right
    case mixMulAdd(name: String, const: Int)                 // NEW: LCG-like mix
    case cmpEq(lhs: String, rhs: String, out: String)
    case cmpLT(lhs: String, rhs: String, out: String)
    case cmpGT(lhs: String, rhs: String, out: String)
    case popCount(name: String, out: String)             // NEW: population count
    case leadingZeros(name: String, out: String)         // NEW: leading zero bit count
    case byteSwap(name: String)                          // NEW: byte swap
    case setUUIDString(name: String)                     // NEW: generate UUID string
    case compareUUID(lhs: String, rhs: String, outInt: String) // NEW: compare UUID strings
    case setDateNowString(name: String)                  // NEW: current ISO8601 date string
    case compareDateStrings(lhs: String, rhs: String, outInt: String) // NEW: compare parsed dates

    // вызовы через протокол/динамическую диспетчеризацию
    case opApply(lhs: String, rhs: String, selector: String, out: String) // NEW

    // строки
    case setString(name: String, value: String)
    case concat(lhs: String, rhs: String, out: String)
    case setStringFromInt(name: String, intVar: String)
    case replaceInString(name: String, of: String, with: String)
    case upper(name: String)
    case lower(name: String)
    case prefixToLen(name: String, lenVar: String)
    case suffixToLen(name: String, lenVar: String)
    case trimWS(name: String)
    case length(name: String, outInt: String)
    case contains(haystack: String, needle: String, outInt: String)
    case hasPrefixVar(s: String, pref: String, outInt: String)
    case hasSuffixVar(s: String, suff: String, outInt: String)

    // коллекции
    case arrayAppend(valueFrom: String)
    case arrayPopIfAny
    case insertAtZero(valueFrom: String)
    case removeAtIndex(indexVar: String)
    case reverseArray
    case sortAscending
    case arrayGet(indexVar: String, outInt: String)
    case arraySet(indexVar: String, valueVar: String)
    case arraySum(outInt: String)
    case arrayMapAbs
    case arrayRotateLeft(kVar: String)        // NEW
    case arrayPrefixSum                       // NEW

    case dictSet(keyFrom: String, valueFrom: String)
    case pushUniqueToDict(keyFrom: String, valueFrom: String) // was defined, now used
    case incrementValue(keyFrom: String, byVar: String)
    case removeKey(keyFrom: String)
    case dictGetOrZero(keyFrom: String, outInt: String)
    case dictCount(outInt: String)

    // управление
    case ifPositive(varName: String, then: [Instruction], `else`: [Instruction])
    case ifEqualsZero(varName: String, then: [Instruction], `else`: [Instruction])
    case loop(timesVar: String, body: [Instruction])
    case whileDecrementing(varName: String, body: [Instruction])
    case repeatDecrement(varName: String, guardVar: String, body: [Instruction]) // NEW
    case switchMod3(varName: String, case0: [Instruction], case1: [Instruction], case2: [Instruction])
    case switchBucket100(varName: String, small: [Instruction], medium: [Instruction], large: [Instruction], other: [Instruction]) // NEW ranges
    case scopedDefer(body: [Instruction], deferred: [Instruction]) // NEW: do { defer { ... } ... }
    case tryMix(name: String, out: String) // NEW: do/try/catch with throwing helper

    case applyClosureAddCap(capture: String, target: String) // NEW: closure captures

    case nop
}

private struct InstructionBudget {
    private(set) var remaining: Int
    mutating func consume(_ n: Int = 1) -> Bool {
        guard remaining >= n else { return false }
        remaining -= n
        return true
    }
}

// MARK: - Генератор дерева

private struct Generator {
    var rng: SplitMix64
    let maxDepth: Int
    let pools: VarPools

    mutating func pickIntVar() -> String { pools.ints[rng.nextInt(in: 0...(pools.ints.count-1))] }
    mutating func pickStringVar() -> String { pools.strings[rng.nextInt(in: 0...(pools.strings.count-1))] }

    mutating func makeFlatInstruction(budget: inout InstructionBudget) -> Instruction? {
        guard budget.consume() else { return nil }
        switch rng.nextInt(in: 0...67) { // расширили диапазон
        // --- числа (старые) ---
        case 0:  return .setInt(name: pickIntVar(), value: rng.nextInt(in: -9...9))
        case 1:  return .add(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 2:  return .sub(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 3:  return .mul(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 4:  return .divNZ(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 5:  return .modNZ(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 6:  return .absVar(name: pickIntVar())
        case 7:  return .negate(name: pickIntVar())
        case 8:  return .incByConst(name: pickIntVar(), delta: [-3,-2,-1,1,2,3][rng.nextInt(in: 0...5)])
        case 9:  return .minAssign(out: pickIntVar(), a: pickIntVar(), b: pickIntVar())
        case 10: return .maxAssign(out: pickIntVar(), a: pickIntVar(), b: pickIntVar())
        case 11: return .clamp(name: pickIntVar(), minVar: pickIntVar(), maxVar: pickIntVar())

        // --- числа (новые) ---
        case 12: return .bitAnd(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 13: return .bitOr(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 14: return .bitXor(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 15: return .bitNot(name: pickIntVar())
        case 16: return .shiftLeft(name: pickIntVar(), byVar: pickIntVar())
        case 17: return .shiftRight(name: pickIntVar(), byVar: pickIntVar())
        case 18: return .rotl(lhs: pickIntVar(), by: pickIntVar(), out: pickIntVar())
        case 19: return .rotr(lhs: pickIntVar(), by: pickIntVar(), out: pickIntVar())
        case 20: return .mixMulAdd(name: pickIntVar(), const: [1664525, 22695477, 1103515245][rng.nextInt(in: 0...2)])
        case 21: return .cmpEq(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 22: return .cmpLT(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 23: return .cmpGT(lhs: pickIntVar(), rhs: pickIntVar(), out: pickIntVar())
        case 24: return .opApply(lhs: pickIntVar(), rhs: pickIntVar(), selector: pickIntVar(), out: pickIntVar())

        // --- строки ---
        case 25: return .setString(name: pickStringVar(), value: ["foo","bar","baz","qux","swift"][rng.nextInt(in: 0...4)])
        case 26: return .concat(lhs: pickStringVar(), rhs: pickStringVar(), out: pickStringVar())
        case 27: return .setStringFromInt(name: pickStringVar(), intVar: pickIntVar())
        case 28:
            let pairs = [("a","o"),("foo","bar"),("swift","SWIFT"),("x","xx"),("qu","kw")]
            let p = pairs[rng.nextInt(in: 0...(pairs.count-1))]
            return .replaceInString(name: pickStringVar(), of: p.0, with: p.1)
        case 29: return .upper(name: pickStringVar())
        case 30: return .lower(name: pickStringVar())
        case 31: return .prefixToLen(name: pickStringVar(), lenVar: pickIntVar())
        case 32: return .suffixToLen(name: pickStringVar(), lenVar: pickIntVar())
        case 33: return .trimWS(name: pickStringVar())
        case 34: return .length(name: pickStringVar(), outInt: pickIntVar())
        case 35: return .contains(haystack: pickStringVar(), needle: pickStringVar(), outInt: pickIntVar())
        case 36: return .hasPrefixVar(s: pickStringVar(), pref: pickStringVar(), outInt: pickIntVar())
        case 37: return .hasSuffixVar(s: pickStringVar(), suff: pickStringVar(), outInt: pickIntVar())

        // --- массив/словарь ---
        case 38: return .arrayAppend(valueFrom: pickIntVar())
        case 39: return .arrayPopIfAny
        case 40: return .insertAtZero(valueFrom: pickIntVar())
        case 41: return .removeAtIndex(indexVar: pickIntVar())
        case 42: return .reverseArray
        case 43: return .sortAscending
        case 44: return .arrayGet(indexVar: pickIntVar(), outInt: pickIntVar())
        case 45: return .arraySet(indexVar: pickIntVar(), valueVar: pickIntVar())
        case 46: return .arraySum(outInt: pickIntVar())
        case 47: return .arrayMapAbs
        case 48: return .arrayRotateLeft(kVar: pickIntVar())
        case 49: return .arrayPrefixSum
        case 50: return .dictSet(keyFrom: pickStringVar(), valueFrom: pickIntVar())
        case 51: return .pushUniqueToDict(keyFrom: pickStringVar(), valueFrom: pickIntVar())
        case 52: return .incrementValue(keyFrom: pickStringVar(), byVar: pickIntVar())
        case 53: return .removeKey(keyFrom: pickStringVar())
        case 54: return .dictGetOrZero(keyFrom: pickStringVar(), outInt: pickIntVar())
        case 55: return .dictCount(outInt: pickIntVar())

        // --- разные ---
        case 56: return .applyClosureAddCap(capture: pickIntVar(), target: pickIntVar())
        case 57: return .tryMix(name: pickIntVar(), out: pickIntVar())
        case 58: return .popCount(name: pickIntVar(), out: pickIntVar())
        case 59: return .leadingZeros(name: pickIntVar(), out: pickIntVar())
        case 60: return .byteSwap(name: pickIntVar())
        case 61: return .setUUIDString(name: pickStringVar())
        case 62: return .compareUUID(lhs: pickStringVar(), rhs: pickStringVar(), outInt: pickIntVar())
        case 63: return .setDateNowString(name: pickStringVar())
        case 64: return .compareDateStrings(lhs: pickStringVar(), rhs: pickStringVar(), outInt: pickIntVar())
        default: return .nop
        }
    }

    mutating func makeNestedInstruction(budget: inout InstructionBudget, depth: Int, maxConsecutiveFlat: Int) -> Instruction? {
        guard budget.consume() else { return nil }
        let choice = rng.nextInt(in: 0...6)
        switch choice {
        case 0:
            let v = pickIntVar()
            let thenBody = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let elseBody: [Instruction] = (rng.nextBool(probabilityTrue: 50) && budget.remaining > 0)
                ? makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
                : []
            return .ifPositive(varName: v, then: thenBody, else: elseBody)
        case 1:
            let v = pickIntVar()
            let thenBody = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let elseBody = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .ifEqualsZero(varName: v, then: thenBody, else: elseBody)
        case 2:
            let t = pickIntVar()
            let body = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .loop(timesVar: t, body: body)
        case 3:
            let v = pickIntVar()
            let body = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .whileDecrementing(varName: v, body: body)
        case 4:
            let v = pickIntVar()
            let c0 = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let c1 = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let c2 = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .switchMod3(varName: v, case0: c0, case1: c1, case2: c2)
        case 5:
            let v = pickIntVar()
            let g = pickIntVar()
            let body = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .repeatDecrement(varName: v, guardVar: g, body: body)
        default:
            let v = pickIntVar()
            let s = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let m = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let l = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            let o = makeBlock(budget: &budget, depth: depth + 1, maxConsecutiveFlat: maxConsecutiveFlat)
            return .switchBucket100(varName: v, small: s, medium: m, large: l, other: o)
        }
    }

    mutating func makeBlock(budget: inout InstructionBudget, depth: Int, maxConsecutiveFlat: Int) -> [Instruction] {
        var block: [Instruction] = []
        var flatRun = 0
        while budget.remaining > 0 {
            let shouldNest: Bool
            if depth >= maxDepth {
                shouldNest = false
            } else if flatRun >= maxConsecutiveFlat {
                shouldNest = true
            } else {
                shouldNest = rng.nextBool(probabilityTrue: 40)
            }

            if shouldNest, let nested = makeNestedInstruction(budget: &budget, depth: depth, maxConsecutiveFlat: maxConsecutiveFlat) {
                block.append(nested)
                flatRun = 0
            } else if let ins = makeFlatInstruction(budget: &budget) {
                block.append(ins)
                flatRun += 1
            } else {
                break
            }

            if depth == 0 && rng.nextBool(probabilityTrue: 15) { break }
        }
        return block
    }
}

// MARK: - Рендерер

private struct Renderer {
    var nameFactory: NameFactory
    let pools: VarPools

    init(nameFactory: NameFactory, pools: VarPools, helperNames: (proto: String, opAdd: String, opBlend: String, choose: String, err: String, maybeThrow: String, hAdd: String, hBlend: String, rotl: String, rotr: String)? = nil) {
        self.nameFactory = nameFactory
        self.pools = pools
        self.helperNames = helperNames
    }
    
    // helper symbols, уникальные в файле
    private var helperNames: (proto: String, opAdd: String, opBlend: String, choose: String, err: String, maybeThrow: String, hAdd: String, hBlend: String, rotl: String, rotr: String)? = nil

    mutating func render(program: [Instruction], seedToken: String, meta: String) -> String {
        var out: [String] = []
        out.append("// === RandomProgram generated ===")
        out.append("// seedToken: \"\(seedToken)\" | \(meta)")
        out.append("import Foundation")

        // Подготовим уникальные имена helper-ов
        let uniq = nameFactory.make("h")
        let proto = "_Op_\(uniq)"
        let opAdd = "_OpAdd_\(uniq)"
        let opBlend = "_OpBlend_\(uniq)"
        let choose = "_chooseOp_\(uniq)"
        let err = "_Err_\(uniq)"
        let maybeThrow = "_maybeThrow_\(uniq)"
        let hAdd = "_h_add_\(uniq)"
        let hBlend = "_h_blend_\(uniq)"
        let rotl = "_rotl_\(uniq)"
        let rotr = "_rotr_\(uniq)"
        helperNames = (proto, opAdd, opBlend, choose, err, maybeThrow, hAdd, hBlend, rotl, rotr)

        // Helpers: протокол + реализации + утилиты
        out.append("""
        protocol \(proto) { func apply(_ a: Int, _ b: Int) -> Int }
        struct \(opAdd): \(proto) { @inline(never) func apply(_ a: Int, _ b: Int) -> Int { \(hAdd)(a, b) } }
        struct \(opBlend): \(proto) { @inline(never) func apply(_ a: Int, _ b: Int) -> Int { \(hBlend)(a, b) } }
        @inline(never)
        func \(hAdd)(_ a: Int, _ b: Int) -> Int { a &+ b }
        @inline(never)
        func \(hBlend)(_ x: Int, _ y: Int) -> Int {
            var z = x
            z ^= (y &<< 1)
            z &+= 0x9E37_79B9
            return z
        }
        func \(choose)(_ t: Int) -> any \(proto) { (t & 1) == 0 ? \(opAdd)() : \(opBlend)() }
        enum \(err): Error { case e }
        @inline(never)
        func \(maybeThrow)(_ x: Int) throws -> Int {
            if (x % 31) == 0 { throw \(err).e }
            var v = x
            v &*= 1_664_525
            v &+= 1_013_904_223
            return v
        }
        @inline(__always)
        func \(rotl)(_ x: Int, _ c: Int) -> Int {
            let s = c & 31
            return (x &<< s) | (x &>> (32 - s))
        }
        @inline(__always)
        func \(rotr)(_ x: Int, _ c: Int) -> Int {
            let s = c & 31
            return (x &>> s) | (x &<< (32 - s))
        }
        """)

        for iName in pools.ints { out.append("var \(iName) = 0") }
        for sName in pools.strings { out.append("var \(sName) = \"\"") }
        out.append("var \(pools.arr): [Int] = []")
        out.append("var \(pools.dict): [String: Int] = [:]")
        out.append("")
        renderBlock(program, into: &out, indent: 0)
        out.append("")
        let all = (pools.ints + pools.strings + [pools.arr, pools.dict]).joined(separator: ", ")
        out.append("_ = (\(all))")
        return out.joined(separator: "\n")
    }

    private mutating func renderBlock(_ block: [Instruction], into out: inout [String], indent: Int) {
        let ind = String(repeating: "    ", count: indent)
        guard let helpers = helperNames else { return }
        for ins in block {
            switch ins {
            // --- числа ---
            case let .setInt(name, value):
                out.append("\(ind)\(name) = \(value)")
            case let .add(l, r, o):
                out.append("\(ind)\(o) = \(l) + \(r)")
            case let .sub(l, r, o):
                out.append("\(ind)\(o) = \(l) - \(r)")
            case let .mul(l, r, o):
                out.append("\(ind)\(o) = \(l) * \(r)")
            case let .divNZ(l, r, o):
                let t = nameFactory.make("tmpd")
                out.append("\(ind)let \(t) = (\(r) == 0) ? 1 : \(r)")
                out.append("\(ind)\(o) = \(l) / \(t)")
            case let .modNZ(l, r, o):
                let t = nameFactory.make("tmpm")
                out.append("\(ind)let \(t) = (\(r) == 0) ? 1 : \(r)")
                out.append("\(ind)\(o) = \(l) % \(t)")
            case let .absVar(v):
                out.append("\(ind)\(v) = Swift.abs(\(v))")
            case let .negate(v):
                out.append("\(ind)\(v) = -\(v)")
            case let .incByConst(v, delta):
                out.append("\(ind)\(v) &+= \(delta)")
            case let .minAssign(o, a, b):
                out.append("\(ind)\(o) = Swift.min(\(a), \(b))")
            case let .maxAssign(o, a, b):
                out.append("\(ind)\(o) = Swift.max(\(a), \(b))")
            case let .clamp(v, lo, hi):
                let t1 = nameFactory.make("tmplo")
                let t2 = nameFactory.make("tmphi")
                out.append("\(ind)let \(t1) = Swift.min(\(lo), \(hi))")
                out.append("\(ind)let \(t2) = Swift.max(\(lo), \(hi))")
                out.append("\(ind)\(v) = Swift.min(Swift.max(\(v), \(t1)), \(t2))")

            case let .bitAnd(l, r, o):
                out.append("\(ind)\(o) = \(l) & \(r)")
            case let .bitOr(l, r, o):
                out.append("\(ind)\(o) = \(l) | \(r)")
            case let .bitXor(l, r, o):
                out.append("\(ind)\(o) = \(l) ^ \(r)")
            case let .bitNot(v):
                out.append("\(ind)\(v) = ~\(v)")
            case let .shiftLeft(name, byVar):
                let t = nameFactory.make("tmpsh")
                out.append("\(ind)let \(t) = Swift.max(0, Swift.min(31, \(byVar)))")
                out.append("\(ind)\(name) = \(name) << \(t)")
            case let .shiftRight(name, byVar):
                let t = nameFactory.make("tmpsh")
                out.append("\(ind)let \(t) = Swift.max(0, Swift.min(31, \(byVar)))")
                out.append("\(ind)\(name) = \(name) >> \(t)")
            case let .rotl(l, by, o):
                let t = nameFactory.make("tmpsh")
                out.append("\(ind)let \(t) = Swift.max(0, Swift.min(31, \(by)))")
                out.append("\(ind)\(o) = \(helpers.rotl)(\(l), \(t))")
            case let .rotr(l, by, o):
                let t = nameFactory.make("tmpsh")
                out.append("\(ind)let \(t) = Swift.max(0, Swift.min(31, \(by)))")
                out.append("\(ind)\(o) = \(helpers.rotr)(\(l), \(t))")
            case let .mixMulAdd(v, c):
                out.append("\(ind)\(v) &*= \(c)")
                out.append("\(ind)\(v) &+= 1013904223")

            case let .cmpEq(l, r, o):
                out.append("\(ind)\(o) = (\(l) == \(r)) ? 1 : 0")
            case let .cmpLT(l, r, o):
                out.append("\(ind)\(o) = (\(l) < \(r)) ? 1 : 0")
            case let .cmpGT(l, r, o):
                out.append("\(ind)\(o) = (\(l) > \(r)) ? 1 : 0")
            case let .popCount(v, o):
                out.append("\(ind)\(o) = \(v).nonzeroBitCount")
            case let .leadingZeros(v, o):
                out.append("\(ind)\(o) = \(v).leadingZeroBitCount")
            case let .byteSwap(v):
                out.append("\(ind)\(v) = \(v).byteSwapped")

            case let .opApply(l, r, sel, o):
                let opVar = nameFactory.make("tmpop")
                out.append("\(ind)let \(opVar): any \(helpers.proto) = \(helpers.choose)(Swift.abs(\(sel)))")
                out.append("\(ind)\(o) = \(opVar).apply(\(l), \(r))")

            // --- строки ---
            case let .setString(name, value):
                out.append("\(ind)\(name) = \"\(value)\"")
            case let .concat(l, r, o):
                out.append("\(ind)\(o) = \(l) + \(r)")
            case let .setStringFromInt(name, iv):
                out.append("\(ind)\(name) = String(\(iv))")
            case let .replaceInString(name, of, with):
                out.append("\(ind)\(name) = \(name).replacingOccurrences(of: \"\(of)\", with: \"\(with)\")")
            case let .upper(name):
                out.append("\(ind)\(name) = \(name).uppercased()")
            case let .lower(name):
                out.append("\(ind)\(name) = \(name).lowercased()")
            case let .prefixToLen(name, lenVar):
                let t = nameFactory.make("tmplen")
                out.append("\(ind)let \(t) = Swift.max(0, \(lenVar))")
                out.append("\(ind)\(name) = String(\(name).prefix(\(t)))")
            case let .suffixToLen(name, lenVar):
                let t = nameFactory.make("tmplen")
                out.append("\(ind)let \(t) = Swift.max(0, \(lenVar))")
                out.append("\(ind)\(name) = String(\(name).suffix(\(t)))")
            case let .trimWS(name):
                out.append("\(ind)\(name) = \(name).trimmingCharacters(in: .whitespacesAndNewlines)")
            case let .length(s, outI):
                out.append("\(ind)\(outI) = \(s).count")
            case let .contains(hay, nee, outI):
                out.append("\(ind)\(outI) = \(hay).contains(\(nee)) ? 1 : 0")
            case let .hasPrefixVar(s, pref, outI):
                out.append("\(ind)\(outI) = \(s).hasPrefix(\(pref)) ? 1 : 0")
            case let .hasSuffixVar(s, suff, outI):
                out.append("\(ind)\(outI) = \(s).hasSuffix(\(suff)) ? 1 : 0")
            case let .setUUIDString(name):
                out.append("\(ind)\(name) = UUID().uuidString")
            case let .compareUUID(l, r, outI):
                out.append("\(ind)if let u1 = UUID(uuidString: \(l)), let u2 = UUID(uuidString: \(r)) { \(outI) = (u1 == u2) ? 1 : 0 } else { \(outI) = 0 }")
            case let .setDateNowString(name):
                out.append("\(ind)do { let df = ISO8601DateFormatter(); \(name) = df.string(from: Date()) }")
            case let .compareDateStrings(l, r, outI):
                out.append("\(ind)do { let df = ISO8601DateFormatter(); if let d1 = df.date(from: \(l)), let d2 = df.date(from: \(r)) { if d1 < d2 { \(outI) = -1 } else if d1 > d2 { \(outI) = 1 } else { \(outI) = 0 } } else { \(outI) = 0 } }")

            // --- массив/словарь ---
            case let .arrayAppend(v):
                out.append("\(ind)\(pools.arr).append(\(v))")
            case .arrayPopIfAny:
                out.append("\(ind)if !\(pools.arr).isEmpty { _ = \(pools.arr).popLast() }")
            case let .insertAtZero(v):
                out.append("\(ind)if \(pools.arr).indices.contains(0) { \(pools.arr).insert(\(v), at: 0) } else { \(pools.arr).append(\(v)) }")
            case let .removeAtIndex(idxV):
                out.append("\(ind)if \(idxV) >= 0 && \(idxV) < \(pools.arr).count { _ = \(pools.arr).remove(at: \(idxV)) }")
            case .reverseArray:
                out.append("\(ind)\(pools.arr).reverse()")
            case .sortAscending:
                out.append("\(ind)\(pools.arr).sort()")
            case let .arrayGet(idxV, outI):
                out.append("\(ind)\(outI) = (\(idxV) >= 0 && \(idxV) < \(pools.arr).count) ? \(pools.arr)[\(idxV)] : 0")
            case let .arraySet(idxV, valV):
                out.append("\(ind)if \(idxV) >= 0 && \(idxV) < \(pools.arr).count { \(pools.arr)[\(idxV)] = \(valV) }")
            case let .arraySum(outI):
                out.append("\(ind)\(outI) = \(pools.arr).reduce(0, +)")
            case .arrayMapAbs:
                out.append("\(ind)\(pools.arr) = \(pools.arr).map { Swift.abs($0) }")
            case let .arrayRotateLeft(kVar):
                let t = nameFactory.make("tmparr")
                let k = nameFactory.make("tmpk")
                out.append("\(ind)if !\(pools.arr).isEmpty {")
                out.append("\(ind)    let \(k) = Swift.abs(\(kVar)) % \(pools.arr).count")
                out.append("\(ind)    let head = \(pools.arr).prefix(\(k))")
                out.append("\(ind)    let tail = \(pools.arr).dropFirst(\(k))")
                out.append("\(ind)    let \(t) = Array(tail) + Array(head)")
                out.append("\(ind)    \(pools.arr) = \(t)")
                out.append("\(ind)}")
            case .arrayPrefixSum:
                let acc = nameFactory.make("tmpacc")
                out.append("\(ind)do { var \(acc) = 0; \(pools.arr) = \(pools.arr).map { \(acc) &+= $0; return \(acc) } }")

            case let .dictSet(k, v):
                out.append("\(ind)\(pools.dict)[\(k)] = \(v)")
            case let .pushUniqueToDict(k, v):
                out.append("\(ind)if \(pools.dict)[\(k)] == nil { \(pools.dict)[\(k)] = \(v) }")
            case let .incrementValue(k, byV):
                out.append("\(ind)\(pools.dict)[\(k)] = (\(pools.dict)[\(k)] ?? 0) + \(byV)")
            case let .removeKey(k):
                out.append("\(ind)\(pools.dict).removeValue(forKey: \(k))")
            case let .dictGetOrZero(k, outI):
                out.append("\(ind)\(outI) = \(pools.dict)[\(k)] ?? 0")
            case let .dictCount(outI):
                out.append("\(ind)\(outI) = \(pools.dict).count")

            // --- управление ---
            case let .ifPositive(v, thenB, elseB):
                out.append("\(ind)if \(v) > 0 {")
                renderBlock(thenB, into: &out, indent: indent + 1)
                if !elseB.isEmpty {
                    out.append("\(ind)} else {")
                    renderBlock(elseB, into: &out, indent: indent + 1)
                }
                out.append("\(ind)}")

            case let .ifEqualsZero(v, thenB, elseB):
                out.append("\(ind)if \(v) == 0 {")
                renderBlock(thenB, into: &out, indent: indent + 1)
                out.append("\(ind)} else {")
                renderBlock(elseB, into: &out, indent: indent + 1)
                out.append("\(ind)}")

            case let .loop(tVar, body):
                let t = nameFactory.make("tmpt")
                out.append("\(ind)do {")
                out.append("\(ind)    let \(t) = max(0, min(32, \(tVar)))")
                out.append("\(ind)    if \(t) > 0 {")
                out.append("\(ind)        for _ in 0..<( \(t) ) {")
                renderBlock(body, into: &out, indent: indent + 3)
                out.append("\(ind)        }")
                out.append("\(ind)    }")
                out.append("\(ind)}")

            case let .whileDecrementing(v, body):
                let g = nameFactory.make("tmpw")
                out.append("\(ind)do {")
                out.append("\(ind)    var \(g) = 0")
                out.append("\(ind)    while \(v) > 0 && \(g) < 64 {")
                renderBlock(body, into: &out, indent: indent + 2)
                out.append("\(ind)        \(v) -= 1")
                out.append("\(ind)        \(g) += 1")
                out.append("\(ind)    }")
                out.append("\(ind)}")

            case let .repeatDecrement(v, guardV, body):
                let g = nameFactory.make("tmpr")
                out.append("\(ind)do {")
                out.append("\(ind)    var \(g) = max(0, min(32, \(guardV)))")
                out.append("\(ind)    repeat {")
                renderBlock(body, into: &out, indent: indent + 2)
                out.append("\(ind)        \(g) -= 1")
                out.append("\(ind)        \(v) -= 1")
                out.append("\(ind)    } while \(v) > 0 && \(g) > 0")
                out.append("\(ind)}")

            case let .switchMod3(v, c0, c1, c2):
                let t = nameFactory.make("tmps")
                out.append("\(ind)let \(t) = Swift.abs(\(v)) % 3")
                out.append("\(ind)switch \(t) {")
                out.append("\(ind)case 0:")
                renderBlock(c0, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)case 1:")
                renderBlock(c1, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)default:")
                renderBlock(c2, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)}")

            case let .switchBucket100(v, small, medium, large, other):
                let t = nameFactory.make("tmpb")
                out.append("\(ind)let \(t) = Swift.abs(\(v)) % 100")
                out.append("\(ind)switch \(t) {")
                out.append("\(ind)case 0...24:")
                renderBlock(small, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)case 25...49:")
                renderBlock(medium, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)case 50...74:")
                renderBlock(large, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)default:")
                renderBlock(other, into: &out, indent: indent + 1)
                out.append("\(ind)    break")
                out.append("\(ind)}")

            case let .scopedDefer(body, deferred):
                out.append("\(ind)do {")
                out.append("\(ind)    defer {")
                renderBlock(deferred, into: &out, indent: indent + 2)
                out.append("\(ind)    }")
                renderBlock(body, into: &out, indent: indent + 1)
                out.append("\(ind)}")

            case let .tryMix(v, o):
                out.append("\(ind)do {")
                out.append("\(ind)    do {")
                out.append("\(ind)        \(o) = try \(helpers.maybeThrow)(\(v))")
                out.append("\(ind)    } catch {")
                out.append("\(ind)        \(o) ^= 0x5A5A")
                out.append("\(ind)    }")
                out.append("\(ind)}")

            case let .applyClosureAddCap(capture, target):
                let f = nameFactory.make("tmpf")
                out.append("\(ind)let \(f): (Int) -> Int = { x in x &+ \(capture) }")
                out.append("\(ind)\(target) = \(f)(\(target))")

            case .nop:
                out.append("\(ind)// nop")
            }
        }
    }
}

// MARK: - Публичный фасад

public enum FakeCallsGenerator {
    public struct RenderResult {
        public let code: String
        public let instructionCount: Int
    }

    /// Генерирует детерминированный по seedToken Swift-код с именами в формате:
    /// {base}_{Module}{ParentContainer}{TemplateFileName}_{count}
    public static func render(
        seedToken: String,
        maxInstructions: Int,
        maxDepth: Int = 5,                  // увеличили глубину по умолчанию
        maxConsecutiveFlat: Int = 4,
        module: String,
        parentContainer: String,
        templateFileName: String,
        intVarCount: Int = 7,               // больше переменных => больше комбинаций
        stringVarCount: Int = 6
    ) -> RenderResult {
        precondition(intVarCount > 0 && stringVarCount > 0, "Need at least 1 int and 1 string var")

        var factory = NameFactory(module: module, parent: parentContainer, template: templateFileName, counter: 0)
        var intNames: [String] = []
        var strNames: [String] = []
        for _ in 0..<intVarCount { intNames.append(factory.make("i")) }
        for _ in 0..<stringVarCount { strNames.append(factory.make("s")) }
        let arrName = factory.make("arr")
        let dictName = factory.make("dict")
        let pools = VarPools(ints: intNames, strings: strNames, arr: arrName, dict: dictName)

        var gen = Generator(rng: SplitMix64(seed: fnv1a64(seedToken)), maxDepth: maxDepth, pools: pools)
        var budget = InstructionBudget(remaining: max(1, maxInstructions))
        let program = gen.makeBlock(budget: &budget, depth: 0, maxConsecutiveFlat: max(1, maxConsecutiveFlat))

        var renderer = Renderer(nameFactory: factory, pools: pools)
        let meta = "maxInstructions=\(maxInstructions), maxDepth=\(maxDepth), maxConsecutiveFlat=\(maxConsecutiveFlat)"
        let code = renderer.render(program: program, seedToken: seedToken, meta: meta)
        return RenderResult(code: code, instructionCount: program.count)
    }
}


