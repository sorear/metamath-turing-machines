from sys import argv, stderr
name = argv[1]
inline_iters = int(argv[2])
emit_align = int(argv[3])
with open("lam_pre.nql") as a, open(f"{name}.blc") as b, open(f"lam_{name}.nql", "w") as c:
    a2 = a.read()
    b2 = b.read().split("\n")[-1]
# if 1:
#     a2 = name
#     b2 = name
#     c = 1
    prog = []
    prefix = ""
    vardepth = 0
    for i in b2:
        if prefix == "":
            prefix = i
            vardepth = 0
        elif prefix == "1":
            if i == "1":
                vardepth += 1
            elif i == "0":
                # variable
                prog.append((0,vardepth))
                prefix = ""
                while 1:
                    if len(prog) >= 2 and prog[-2] == (-1,) and prog[-1][0] >= 0:
                        # lambda
                        x = prog.pop()
                        y = prog.pop()
                        prog.append((1,x))
                    elif len(prog) >= 3 and prog[-3] == (-2,) and prog[-1][0] >= 0 and prog[-2][0] >= 0:
                        # apply
                        x = prog.pop() # arg
                        y = prog.pop() # fun
                        z = prog.pop()
                        prog.append((2,y,x))
                    else:
                        break
        elif prefix == "0":
            if i == "0":
                # lambda without body
                prog.append((-1,))
            elif i == "1":
                # apply without args
                prog.append((-2,))
            prefix = ""
    assert prefix == ""
    assert len(prog) == 1
    maxfreevar = {}
    parents = {}
    def analyze(maxfreevar, parents, x):
        def count(d,i):
            if i not in d:
                d[i] = 0
            d[i] += 1
        if x not in parents:
            # if x == (0,0):
            #     print("found 0,0")
            # if x == (0,1):
            #     print("found 0,1")
            parents[x] = {}
        if x[0] == 0:
            # variable
            maxfreevar[x] = x[1]
        elif x[0] == 1:
            # lambda
            analyze(maxfreevar, parents, x[1])
            count(parents[x[1]], ("lambda",))
            maxfreevar[x] = maxfreevar[x[1]] - 1 if maxfreevar[x[1]] >= 0 else -1
        else:
            # application
            analyze(maxfreevar, parents, x[1])
            analyze(maxfreevar, parents, x[2])
            count(parents[x[1]], ("fun", x[2]))
            count(parents[x[2]], ("arg", x[1]))
            maxfreevar[x] = max(maxfreevar[x[1]], maxfreevar[x[2]])
    def subst(fun, arg, var):
        if fun[0] == 0:
            # variable
            if fun[1] == var:
                return arg
            else:
                return fun
        elif fun[0] == 1:
            # lambda
            return (1,subst(fun[1], arg, var + 1))
        elif fun[0] == 2:
            # application
            return (2,subst(fun[1], arg, var),subst(fun[2], arg, var))
    def simplify(x):
        if x[0] == 0:
            # variable
            return x
        elif x[0] == 1:
            # lambda
            return (1,simplify(x[1]))
        else:
            # application
            fun = x[1]
            arg = x[2]
            fun2 = simplify(x[1])
            arg2 = simplify(x[2])
            # fun,arg = fun2,arg2
            # print(fun,arg)
            if fun[0] != 1:
                # print(1)
                return (2,fun2,arg2)
            if fun not in maxfreevar or arg not in maxfreevar:
                # print(2)
                return (2,fun2,arg2)
            if len(parents[fun]) != 1:
                # print(3)
                return (2,fun2,arg2)
            if maxfreevar[arg] > -1:
                # print(4, maxfreevar[arg])
                return (2,fun2,arg2)
            # stderr.write(str((parents[fun],maxfreevar[arg]))+"\n")
            # 1/0
            # print("Inlined")
            return subst(fun[1], arg, 0)
    for i in range(inline_iters):
        parents = {}
        maxfreevar = {}
        analyze(maxfreevar, parents, prog[0])
        prog[0] = simplify(prog[0])
    def emit(x):
        if x[0] == 0:
            # every push_x zeroes t2, and it starts at 0
            if x[1] == 0:
                return "push_var(t2);"
            return f"t2 = t2 + {x[1]}; push_var(t2);"
        elif x[0] == 1:
            return f"{emit(x[1])} push_lam();"
        elif x[0] == 2:
            return f"{emit(x[1])} {emit(x[2])} push_app();"
    def emit2(x):
        push_var0 = ("push_var(t2);", 128, 7)
        push_lam = ("push_lam();", 64, 6)
        push_app = ("push_app();", 256, 8)
        def push_var(n):
            if n == 0:
                return push_var0
            return (f"t2 = t2 + {n}; push_var(t2);", 256, 7)
        def join(xs): 
            size = 0
            align = 0
            for x in xs:
                # round up to multiple of (1<<x[2])
                # print(size, x[2], (size + ((1 << x[2]) - 1)) & -(1 << x[2]))
                size = (size + ((1 << x[2]) - 1)) & -(1 << x[2])
                size += x[1]
                align = max(align, x[2])
            return (" ".join((x[0] for x in xs)),size,align)
        # print(join([("t2 = t2 + 257;", 129, 0), push_var0]))
        # 1/0
        shared = 0
        unique = 0
        def emit3(x):
            nonlocal shared, unique
            out = ("", 0, 0)
            if x[0] == 0:
                out = push_var(x[1])
            elif x[0] == 1:
                out = join([emit3(x[1]), push_lam])
            elif x[0] == 2:
                out = join([emit3(x[1]), emit3(x[2]), push_app])
            # if sum((1 for i in parents[x])) > 1:
            if len(parents[x]) > 1:
                # shared
                align = (out[1]-1).bit_length() if out[1] > 0 else 0
                code = f"align_{align}(); {out[0]} align_{align}();" if align > out[2] else out[0]
                out = (code, 1 << align, align)
                shared += 1
            else:
                unique += 1
            return out
        parents = {}
        maxfreevar = {}
        analyze(maxfreevar, parents, x)
        # print(parents)
        y = emit3(x)
        # print(shared, unique)
        # print(y)
        return y[0]
    def blc(x):
        if x[0] == 0:
            return "1"+"1"*x[1]+"0"
        elif x[0] == 1:
            return f"00{blc(x[1])}"
        elif x[0] == 2:
            return f"01{blc(x[1])}{blc(x[2])}"
    # print(blc(prog[0]))
    c.write(a2.replace("/* program goes here */", emit2(prog[0]) if emit_align else emit(prog[0])))