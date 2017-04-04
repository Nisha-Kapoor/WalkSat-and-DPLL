import copy
import collections
#from utils import Expr
import random
kb=[]
item=[]
clause=[]
d={}
read_file = open("input.txt", "r")
first_line=read_file.readline()
numbers_str=first_line.split()
m = int(numbers_str[0])
n = int(numbers_str[1])



for i in range(1,m+1):
    for j in range(1,n+1):
        item.append(str(i)+" "+str(j))
        if j<n:
            item.append("V")
        for k in range(j+1,n+1):
            clause.append("~"+str(i)+" "+str(j))
            clause.append("V")
            clause.append("~"+str(i)+" "+str(k))
            kb.append(clause)
            clause = []

    kb.append(item)
    item=[]


clause=[]
line=read_file.readline()
while line:
    next_line=line.split()
    if next_line[2]=="E":
        for i in range(1,n+1):
            clause.append("~"+next_line[0]+" "+str(i))
            clause.append("V")
            clause.append("~" +next_line[1]+" "+str(i))

            kb.append(clause)
            clause = []
                elif next_line[2]=="F":
        for i in range(1,n+1):
            clause.append("~" + next_line[0]+" "+str(i))
            clause.append("V")
            clause.append(next_line[1]+" "+str(i))
            #print clause
            kb.append(clause)
            clause = []
            clause.append(next_line[0] +" "+ str(i))
            clause.append("V")
            clause.append("~" + next_line[1] +" "+ str(i))
            #print clause
            kb.append(clause)
            clause = []
            
    line=read_file.readline()
    #print "Print line"+line
    next_line=list(line)


#print kb


def dpll_satisfiable():
    symbols=[]
    #print kb
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            symbols.append(str(i)+" " + str(j))
    #print "symbols %s"%symbols
    return dpll(kb, symbols, {})


def dpll(clauses, symbols, mod):
    unknown = []
    #print type(unknown)
    true=[]
    #print type(true)
    if mod:
        for c in clauses:
            val = checky(c, mod)
            #print "val %s"%val
            if val is False:
                #print "returning false"
                return False
            if val is not True:
                unknown.append(c)
            if val is True:
                true.append(c);

    if len(true)==len(clauses):
        return mod
    P, value = pureSymbol(symbols, unknown)
    #print type(P)
    #print "p, value %s %s"%(P,value)
    if P != None:
        #print "going to p not none"
        return dpll(clauses, update(symbols,P), expand(mod, P, value))
    P, value = unitClause(clauses, mod)
    #print "p, value %s %s" % (P, value)
    if P != None:
        return dpll(clauses, update(symbols,P), expand(mod, P, value))
    if not symbols:
        print "Symbols empty"
    P, symbols = symbols[0], symbols[1:]
    #print "p symbols %s %s"%(P,symbols)
    return (dpll(clauses, symbols, expand(mod, P, True)) or
            dpll(clauses, symbols, expand(mod, P, False)))


def update(symbols,P):
    #print "printing symbols %s" % symbols
    symbols=[item for item in symbols if item not in P]
    #print "printing symbols %s"%symbols
    return symbols

def expand(s, var, val):
    #print "In expand"
    s2 = copy.deepcopy(s)
    s2[var] = val
    #print s2
    return s2

def pureSymbol(symbols, clauses):
    for s in symbols:
        #print "s %s"%s
        pos, neg = False, False
        for c in clauses:
            if not pos and s in c:
                #print "s,c %s%s"%(s,c)
                pos = True
            if not neg and ("~"+s) in c:
                #print "s,c %s%s" % (s, c)
                neg = True
        #print "Pos, neg %s %s"%(neg,pos)
        if pos != neg:
            return s, pos
    return None, None

def unitClause(clauses, mod):
    #print "In unit"
    for clause in clauses:
        #P,value=None,None
        P, value = unit_clause_assign(clause, mod)
        if P!=None:
            return P, value
    return None, None



def unit_clause_assign(clause, model):
    "In unit %s%s"%(clause, model)
    cl=[]
    P, value = None, None
    for literal in clause:
        if literal != 'V':
            cl.append(literal)
    for l in cl:

        sym, positive = inspect_literal(l)
        if sym in model:
            if model[sym] == positive:
                return None, None  # clause already True
        elif P:
            return None, None      # more than 1 unbound variable
        else:
            P, value = sym, positive
    return P, value






def inspect_literal(literal):
    if literal[0] == '~':
        return getSymbol(literal),False
    else:
        return literal,True



model={}
def WalkSat(p=0.6,maxFlips=1000):
    symbols = set()
    global model
    for i in range(1, m + 1):
        for j in range(1, n + 1):
            model[str(i) + str(j)] = random.choice([True, False])
    #symbols=set(range(1,m+1))
    #model={s: str(s)+str(random.choice(range(1,n+1))) for s in symbols}
    #print "model %s"%model
    for i in range(0, maxFlips):
        #print "In max for loop"
        satisfied, unsatisfied = [], []
        for clause in kb:
            #print clause
            (satisfied if check(clause, model) else unsatisfied).append(clause)
        #print "sat %s"%len(satisfied)
        #print "unsat %s" % len(unsatisfied)
        #print "model %s"%model
        if not unsatisfied:  # if model satisfies all the clauses
            #print "I am empty %s"%unsatisfied
            return model
        cl = random.choice(unsatisfied)
        #print "random cl %s"%cl
        count = {}
        if probability(p):
            t=selectRandom(cl)
            #print "t %s"%t
            sym=getSymbol(t)
            #print "sym %s"%sym

        else:
            for q in cl:

                if q!='V':
                    #print "q %s " % q
                    s=getSymbol(q)
                    model[s] = not model[s]
                    maxi=float("-inf")
                    a=[]
                    for c in kb:
                        if check(c,model):
                            a.append(c)
                    if maxi< len(a):
                        #maxi=len(a)
                        sym=s
                    model[s] = not model[s]
            #print "count %s"%count
        #print "clause after %s" % cl
        #print "Flipping %s"%sym
        model[sym]=not model.get(sym)
        # If no solution is found within the flip limit, we return failure

    return None

def probability(p):
    x=random.uniform(0,1)
    if (x<p):
        return True
    else:
        return False

def check(clause, model):
    #print "check %s%s"%(clause,model)
    for c in clause:
        if c!='V':
            if c[0]=='~':
                if c[1:] in model and model[c[1:]]==False:
                    return True
            else:
                if c in model and model[c]==True:
                    return True
    return False

def checky(clause, model):
    #print  clause, model
    false=[]
    cl=[]
    for c in clause:
        if c!='V':
            cl.append(c);
            if c[0]=='~':
                if c[1:] in model and model[c[1:]]==False:
                    return True
                elif c[1:] in model and model[c[1:]]==True:
                    false.append(c)
            else:
                if c in model and model[c]==True:
                    return True
                elif c in model and model[c]==False:
                    false.append(c)
    if len(false)==len(cl):
        return False
    return None


def selectRandom(clause):
    a = random.choice(clause)
    while a == 'V':
        a=random.choice(clause)
    else:
        return a

def getSymbol(sym):
    s = sym[0]
    if s == '~':
        s = sym[1:]
    else:
        s=sym
        #print "s %s"%s
    return s



#res=resolution()
#print "The result is %s"%res

answer=dpll_satisfiable()
#print "The result is %s"%answer
if answer==False:
    ans="no"
else:
    ans="yes"

    final={}
    queue=[]
    for f in answer:
        if answer[f]==True:
            a=f.split();
            #print a
            key=int(a[0])
            final[key]=a[1]
    final= sorted(final.items())
    #print sorted(final)
    for f in final:
        queue.append("%s %s"%(f[0],f[1]))

f = open("output.txt", "w")
f.write(ans+"\n")
if ans=="yes":
    for q in queue:
        f.write(q+"\n")
f.close()



'''answer=WalkSat()
#print "answer %s" %answer
if answer is None:
    ans= "no"
else:
    ans="yes"
    final={}
    queue=[]
    for f in answer:
        if answer[f]==True:
             final[f[0]]=f[1]
    final= sorted(final.items())
    #print final
    for f in final:
        queue.append("%s %s"%(f[0],f[1]))

f = open("output.txt", "w")
f.write(ans+"\n")
if ans=="yes":
    for q in queue:
        f.write(q+"\n")
f.close()'''
