from itertools import product
from math import factorial
from functools import reduce

subs = [0,1,3,6,10]   # residues of J0,J1,J3,J6,J10
names = ['J0','J1','J3','J6','J10']

def multinom(exps):
    n = sum(exps)
    d = reduce(lambda a,b:a*b, [factorial(e) for e in exps], 1)
    return factorial(n)//d

def power_part(power, target_res):
    """residue-target part of (sum J_i)^power : dict exps->coeff mod 11"""
    out = {}
    # exps over 5 vars summing to power
    def gen(i, remaining, cur):
        if i==4:
            cur=cur+[remaining]; 
            w = sum(e*s for e,s in zip(cur,subs))%11
            if w==target_res:
                c = multinom(cur)%11
                if c: out[tuple(cur)] = c
            return
        for e in range(remaining+1):
            gen(i+1, remaining-e, cur+[e])
    gen(0,power,[])
    return out

def show(d):
    terms=[]
    for exps,c in sorted(d.items(), key=lambda x:(-x[0][0],x[0])):
        mon=''.join(f'{names[i]}^{exps[i]} ' if exps[i]>1 else (f'{names[i]} ' if exps[i]==1 else '') for i in range(5)).strip()
        terms.append(f'{c}*{mon}')
    return ' + '.join(terms)

P = power_part(7,6)
print("P = [S^7]_6, #monomials =", len(P))
print(show(P))
print()
for r in [3,6,8,9,10]:
    R=power_part(4,r)
    print(f"R_{r} = [S^4]_{r}, #monomials={len(R)}:")
    print(" ", show(R))
