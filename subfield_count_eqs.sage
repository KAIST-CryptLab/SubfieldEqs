from itertools import product, combinations_with_replacement, combinations
from string import ascii_uppercase, ascii_lowercase, digits

#Notation for readability: modified base64, with similarities to normal hex for smaller digits
#Was used in testing.
#0123456789 abcdef...z ABCDEF...Z +/
#b64=digits+ascii_lowercase+ascii_uppercase+'+/'

def subfield_expr(n, m, sbox, *, affine=False, max_deg=2, PROGRESS=True, FINAL_MAT=False):
    #Counting equations for inverse S-box on GF(2^n) over subfield GF(2^m)
    #max_deg: target max degree; almost always fix to 2.
    #GF(2^m) is subfield of GF(2^n), and hence m|n. If not, we do not run the code.
    assert not(n%m)

    #Number of subfield variables for x and y.
    k=n//m

    progress = lambda *args, **kwargs: print(*args, **kwargs) if PROGRESS else None
    final_matrix = lambda *args, **kwargs: print(*args, **kwargs) if FINAL_MAT else None

    #Subfield(G) and its variables
    G.<w>=GF(2**m, repr='int')
    x_vars=', '.join(map(lambda x:f'x{x}', range(k)))
    y_vars=', '.join(map(lambda x:f'y{x}', range(k)))
    vars = G[x_vars+', '+y_vars].gens()
    x_vars=vars[:k]
    y_vars=vars[k:]

    #find an irreducible polynomial
    RG.<a> = PolynomialRing(G)
    for coeffs in product(range(2**m), repeat=k):
        base = G.fetch_int(1)
        for i in coeffs:
            base*=a
            base+=G.fetch_int(i)
        if base.is_irreducible():
            prim = base
            break
    progress('Irreducible Polynomial Found')

    F.<z>=G.extension(prim)
    x,y=F['x, y'].gens()

    #Transform an element in F to k=n/m elements in G
    def F_to_G(val):
        nonlocal F
        coeffs = []
        if m!=1:
            for coeff in F(val):
                coeffs.append(coeff)
        else:
            s=str(val)
            if s.startswith('('):
                s=s[1:-1]
            s=s.split(' + ')
            coeffs.append(int('1' in s))
            coeffs.append(int('z' in s))
            for i in range(2, k):
                coeffs.append(int(f'z^{i}' in s))
        return coeffs[::-1]

    #Transform k elements in G to F
    def G_to_F(vals):
        total = 0
        for val in vals:
            total*=z
            total+=val
        return total

    #Change field item into readable integer
    #i.e. w^2+1 = 5, w^3+w = 10, etc.
    def field_to_int(val):
        return eval(str(val).replace('w', '2').replace('^','**')) #.replace('z', '(2**k)') can be placed in, but is unnecessary

    #Change two field items into sequence of elements of G
    def FF_to_GG(x, y):
        return [*F_to_G(x), *F_to_G(y)]

    #Building Inverse S-box
    inv = {}
    sbox_expr = sbox(x)
    for vals in product(range(2**m), repeat=k):
        fetched = [*map(lambda x:G.fetch_int(x), vals)]
        F_elt = G_to_F(fetched)
        inv[F_elt] = (sbox_expr).subs({x:F_elt})
    progress("S-box Calculated")

    #Constructing the augmented matrix
    aug = [] # Vertical vector for terms of degree less than max_deg of elements of G
    mat = [] # Matrix for values of the corresponding item of aug, for all elements of F
    for d in range(max_deg+1):
        #every term of degree d, according to affine condition
        if affine:
            terms = combinations(vars, d)
        else:
            terms = combinations_with_replacement(vars, d)
        for term in terms:
            #Constructing the target term
            target = G.fetch_int(1)
            for i in term:
                target*=i
            aug.append([target])

            #For every item in inverse S-box, calculate the value for the target term.
            res=[]
            for x_val, y_val in inv.items():
                vals = FF_to_GG(x_val, y_val)
                res.append(target.subs(dict(zip(vars, vals))))
            mat.append(res)

    M=matrix(mat)
    A=matrix(aug)

    row = len(aug)
    col = len(inv)
    progress('Augmented Matrix Constructed')

    # Gaussian Elimination on M augmented with A
    # We cannot augment the two matrices since they have different typing,
    # and therefore the elimination algorithm is implemented manually.
    row_idx = 0
    col_idx = 0

    while row_idx<row and col_idx<col:
        if M[row_idx][col_idx]==0:
            #If for the target row, 0 exists in that particular column,
            #swap with any later row with a nonzero value for that particular column.
            for j in range(row_idx+1, row):
                if M[j][col_idx]!=0:
                    A.swap_rows(row_idx, j)
                    M.swap_rows(row_idx, j)
                    break
            else:
                #If no nonzero row is found, go to the next column.
                col_idx+=1
                continue
        for j in range(row_idx+1, row):
            if row_idx==j: continue
            #We only need REF, not RREF.
            #Therefore, any upper rows are untouched.
            #For RREF, the range may be changed to (0,row).
            s = -M[j][col_idx]/M[row_idx][col_idx] #negative sign unnecessary, but added for clarity/generality
            A.add_multiple_of_row(j, row_idx, s)
            M.add_multiple_of_row(j, row_idx, s)
        #Similarly, rescaling is skipped since this is unnecessary.
        #M.rescale_row(i, 1/M[i][i])
        #M.rescale_row(i, 1/M[i][i])
        row_idx+=1
        col_idx+=1
    progress('Gaussian Elimination Finished')

    #Counting the rows
    n_cnt=0 #Nonzero row count
    z_cnt=0 #Zero row in M, but the corresponding row in A is also zero
    r_cnt=0 #Zero row in M, and the corresponding row in A is nonzero
    s=set() #Set for nonzero augmented items for the zero rows
    for row, term in zip(M, A):
        #print M augmented with A; used in debugging.
        #print(row)
        final_matrix(*map(lambda x:field_to_int(x), row), term)
        for i in row:
            if i!=0:
                #nonzero row
                n_cnt+=1
                break
        else:
            if term==0:
                #zero row with zero term
                z_cnt+=1
            else:
                #zero row with nonzero term
                s.add(term[0])
                r_cnt+=1

    #Our target: r_cnt/s.
    #If we fix m=1, r_cnt should be 7n-1.
        #2n by the equality x^2=x in GF(2)
        #5n-1 from Courtois' research
    return prim, s

if __name__=='__main__':
    for n in range(1,20):
        for m in range(2, n):
            if n%m:
                continue
            k=n//m
            sbox=lambda x:x^(2^n-2)
            prim, s=subfield_expr(n, m, sbox, PROGRESS=False, FINAL_MAT=False)
            print(prim)
            print(s)
            r_cnt=len(s)
            print(f"n={n}, m={m}, k={k}, r_cnt={r_cnt}")