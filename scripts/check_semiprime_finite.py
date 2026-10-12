from sympy import isprime, divisors
# verify bound lemma numerically and finite check
cnt=0
for p in range(3,62):
    if not isprime(p): continue
    for d in divisors(16*(p*p-1)):
        q=d-1
        if q<=p or not isprime(q): continue
        cnt+=1
        n=p*q; s=(p+1)*(q+1)//4
        if (n*n-1)%(s*(s-1))==0: print("COUNTEREX",p,q)
print("checked",cnt)
# sanity: is min prime really <=61 required? check 16 - 16/(p^2q^2) < 15(1+1/p)^4 fails at p=67
p=67; print(15*(1+1/p)**4, 16)
