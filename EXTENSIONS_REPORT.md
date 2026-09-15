# Ten further extensions of the prime-GPF theory

This report records ten mathematical extensions of the three prime-GPF operations

\[
A(p,q)=P^+(p+q+1),\qquad
M(p,q)=P^+(pq+1),\qquad
E_p(q)=P^+(p^q+1),
\]

with prime inputs and anchors.  The mathematical proofs are given below.  Formal Lean status is reported separately and is deliberately stricter than mathematical status.

## Formalization status

| Extension | Mathematical status | Lean status on `extensions-5-6-8-9-10-20260915` |
|---|---|---|
| 1 | proved below | not yet formalized |
| 2 | proved below | not yet formalized |
| 3 | proved below | not yet formalized |
| 4 | proved below | not yet formalized |
| 5 | proved below | core escape and visit-count statements compiler-verified |
| 6 | proved below | finite image bound (9) and deep-image classification (11) compiler-verified; asymptotic ratio (10) not yet formalized |
| 7 | proved below | not yet formalized |
| 8 | proved below | inequalities (14)--(16) compiler-verified; prime-polynomial corollary not yet separately packaged |
| 9 | proved below | Lean proof under branch CI validation |
| 10 | proved below | algebraic separation compiler-verified; dynamical separation not yet formalized |

The verified Lean material is in `PrimeGPF/Extensions.lean`; extension 9 is developed in `PrimeGPF/Extension9.lean`.

---

## Counting lemma

For a finite nonempty set of primes \(T\), put

\[
d=|T|,\qquad C_T=\frac1{d!\prod_{\ell\in T}\log\ell},
\]

and let \(S_T(Y)\) count positive integers at most \(Y\) whose prime factors belong to \(T\). Then

\[
S_T(Y)=C_T(\log Y)^d+O_T((1+\log Y)^{d-1}). \tag{*}
\]

**Proof.** Unique factorization identifies the counted integers with lattice points

\[
e_\ell\ge0,\qquad \sum_{\ell\in T}e_\ell\log\ell\le\log Y.
\]

The simplex has volume \(C_T(\log Y)^d\). Place a unit cube at each lattice point. Their union is sandwiched between the simplex with bound \(\log Y\) and that with bound \(\log Y+\sum_{\ell\in T}\log\ell\). The difference of these volumes is \(O_T((1+\log Y)^{d-1})\), proving (*). ∎

## 1. A logarithm saving for every fixed additive fiber

For

\[
F^+_{a,r}(x)=\#\{q\le x:q\text{ prime},\ A(a,q)=r\},\qquad r\ge3,
\]

if \(r\mid a+1\), the fiber has at most one input. Otherwise set

\[
T=\{\ell\le r:\ell\text{ prime},\ \ell\nmid a+1\},\qquad d=|T|.
\]

Then

\[
\limsup_{x\to\infty}\frac{F^+_{a,r}(x)}{(\log x)^d}\le C_T. \tag{1}
\]

Hence

\[
F^+_{a,r}(x)=O_{a,r}((\log x)^{\pi(r)-1}).
\]

**Proof.** If \(r\mid a+1\) and \(r\mid a+q+1\), then \(r\mid q\), so primality gives \(q=r\). Otherwise take a fiber input \(q>r\). Every prime divisor of \(a+q+1\) is at most \(r\), and none divides \(a+1\), since such a divisor would also divide the prime \(q\), contradicting \(q>r\). Also \(r\mid a+q+1\). Therefore

\[
q\mapsto \frac{a+q+1}{r}
\]

injects these inputs into the \(T\)-smooth integers at most \((x+a+1)/r\). Thus

\[
F^+_{a,r}(x)\le \pi(r)+S_T((x+a+1)/r),
\]

and (*) gives (1). For odd \(a\), \(2\notin T\); for \(a=2\), \(3\notin T\). Hence \(d\le\pi(r)-1\). ∎

Example: for \(a=r=5\), \(T=\{5\}\), so

\[
F^+_{5,5}(x)\le \frac{\log x}{\log5}+O(1).
\]

## 2. A \(1/\zeta(d)\) improvement for multiplicative fibers

Let

\[
F^\times_{a,r}(x)=\#\{q\le x:q\text{ prime},\ M(a,q)=r\}.
\]

The fiber is empty if \(a=r\). Otherwise put

\[
T=\{\ell\le r:\ell\text{ prime},\ \ell\ne a\},\qquad d=|T|.
\]

For \(d\ge2\),

\[
\limsup_{x\to\infty}\frac{F^\times_{a,r}(x)}{(\log x)^d}
\le \frac1{\zeta(d)d!\prod_{\ell\in T}\log\ell}. \tag{2}
\]

**Proof.** The kernel \(aq+1\) is \(T\)-smooth because \(a\nmid aq+1\). For \(q>a\), suppose its exponent vector has gcd \(g>1\), so \(aq+1=u^g\). Then \(u-1\mid aq\), and \(1\le u-1<q\), since \(u\le\sqrt{aq+1}<q\). As \(a,q\) are distinct primes,

\[
u-1\in\{1,a\}.
\]

Thus every nonprimitive kernel belongs to one of the two families

\[
aq+1=2^g\quad\text{or}\quad aq+1=(a+1)^g,
\]

which contribute only \(O_a(\log x)\) possibilities.

For primitive exponent vectors, Möbius inversion and (*) give, with \(L=\log Y\),

\[
V_T(L)=\sum_{g\le L/\min_{\ell\in T}\log\ell}\mu(g)(S_T(e^{L/g})-1)
=\frac{C_T}{\zeta(d)}L^d+o(L^d).
\]

The accumulated error is \(O(L\log L)\) for \(d=2\) and \(O(L^{d-1})\) for \(d\ge3\). Taking \(L=\log(ax+1)\) proves (2). This is an upper-bound coefficient, not an assertion that the prime fiber attains the coefficient. ∎

## 3. The output-5 multiplicative fiber at anchor 2

For prime \(q\),

\[
M(2,q)=5
\]

iff either \(q=2\), or

\[
q=\frac{3^\alpha5^\beta-1}{2},\qquad \alpha,\beta\ge1,\quad \alpha\text{ odd},\quad \gcd(\alpha,\beta)=1. \tag{3}
\]

Every nonexceptional input satisfies \(q\equiv7\pmod{30}\), and

\[
\limsup_{x\to\infty}\frac{F^\times_{2,5}(x)}{(\log x)^2}
\le\frac1{3\zeta(2)\log3\log5}. \tag{4}
\]

**Proof.** For odd \(q\), the odd 5-smooth kernel is

\[
2q+1=3^\alpha5^\beta,\qquad \beta\ge1.
\]

If \(\alpha=0\), then \((5^\beta-1)/2\) is even, so primality forces \(q=2\). Hence \(\alpha\ge1\). Modulo 4, \(\alpha\) is odd. If \(g=\gcd(\alpha,\beta)>1\), then \(g\) is odd. Putting \(t=3^{\alpha/g}5^{\beta/g}\ge15\),

\[
q=\frac{t-1}{2}(1+t+\cdots+t^{g-1}),
\]

contradicting primality. Conversely, (3) directly makes the kernel 5-smooth with greatest prime factor 5. Divisibility by 3 and 5, together with oddness, gives \(q\equiv7\pmod{30}\).

For (4), the unrestricted weighted exponent triangle has leading coefficient \(1/(2\log3\log5)\). Restricting \(\alpha\) to odd values contributes \(1/2\), while coprimality over odd common divisors contributes

\[
\sum_{g\text{ odd}}\frac{\mu(g)}{g^2}=\frac4{3\zeta(2)}.
\]

Multiplying gives (4). The formula still requires the resulting \(q\) to be prime. ∎

## 4. The output-5 multiplicative fiber at anchor 3

For prime \(q\),

\[
M(3,q)=5
\]

iff

\[
q=\frac{2^\alpha5^\beta-1}{3},\qquad
\alpha,\beta\ge1\text{ odd},\quad \gcd(\alpha,\beta)=1. \tag{5}
\]

Every such input satisfies \(q\equiv3\pmod{10}\), and

\[
\limsup_{x\to\infty}\frac{F^\times_{3,5}(x)}{(\log x)^2}
\le\frac1{6\zeta(2)\log2\log5}. \tag{6}
\]

**Proof.** The input \(q=2\) gives output 7. Otherwise the kernel is even, not divisible by 3, and

\[
3q+1=2^\alpha5^\beta,\qquad \alpha,\beta\ge1.
\]

Modulo 3 the exponents have the same parity. If both were even, the kernel would be \(t^2\), and

\[
q=\frac{(t-1)(t+1)}3,
\]

with both resulting factors greater than 1, contradicting primality. Hence both exponents are odd. If \(g=\gcd(\alpha,\beta)>1\), put \(t=2^{\alpha/g}5^{\beta/g}\); then \(t\equiv1\pmod3\) and

\[
q=\frac{t-1}{3}(1+t+\cdots+t^{g-1}),
\]

again contradicting primality. The converse is immediate. Oddness and divisibility of \(3q+1\) by 5 give \(q\equiv3\pmod{10}\).

For (6), the two odd-exponent restrictions contribute \(1/4\), and coprimality contributes \(4/(3\zeta(2))\). ∎

## 5. Explicit exponential escape and sparse orbits

Fix a prime anchor \(a\) and set \(q_{n+1}=E_a(q_n)\). Except for the constant orbit \(a=2,q_0=3\),

\[
q_n+1\ge2^n(q_0+1). \tag{7}
\]

Consequently, for \(X\ge q_0\),

\[
\#\{n\ge0:q_n\le X\}
\le1+\left\lfloor\log_2\frac{X+1}{q_0+1}\right\rfloor. \tag{8}
\]

**Proof.** The prime-exponent theorem gives \(E_a(q)\ge2q+1\) for odd prime \(q\), except \((a,q)=(2,3)\). For \(q=2\), the square-exponent congruence gives \(E_a(2)\ge5=2q+1\). A nonexceptional step therefore outputs at least 5 and cannot subsequently enter the exceptional state 3. Hence

\[
q_{n+1}+1\ge2(q_n+1)
\]

at every step. Induction yields (7), and solving (7) for \(n\) gives (8). ∎

The Lean development proves (7), a discrete natural-log form of (8), and the corresponding finite cardinality bound.

## 6. Iterated exponential images shrink geometrically

Let

\[
I_{a,k}=E_a^k(\mathbb P).
\]

Then

\[
\#(I_{a,k}\cap[2,X])
\le\pi\!\left(\frac{X+1}{2^k}-1\right)+\mathbf1_{a=2}. \tag{9}
\]

Thus

\[
\limsup_{X\to\infty}\frac{\#(I_{a,k}\cap[2,X])}{\pi(X)}\le2^{-k}. \tag{10}
\]

Moreover,

\[
\bigcap_{k\ge1}I_{a,k}=
\begin{cases}
\{3\},&a=2,\\
\varnothing,&a\ne2.
\end{cases} \tag{11}
\]

**Proof.** If a nonexceptional starting prime has its \(k\)-th iterate at most \(X\), (7) gives

\[
q_0\le\frac{X+1}{2^k}-1.
\]

Counting possible starting primes bounds the number of distinct outputs; the exceptional fixed orbit contributes at most one extra value. This proves (9). The prime number theorem then gives (10).

If a nonexceptional prime \(r\) has a \(k\)-step ancestor, then

\[
r+1\ge2^k(q_0+1)\ge3\cdot2^k,
\]

so its ancestry depth is finite. Only \(E_2(3)=3\) has arbitrarily deep ancestry, proving (11). ∎

The Lean development currently proves (9) and the exact all-depth form of (11). The PNT passage to (10) is not yet formalized in this extension module.

## 7. Quantitative rarity of additive-multiplicative collisions

Fix a prime \(a\), put

\[
B_a=a^2+a-1,\qquad R_a=P^+(B_a),
\]

and

\[
T_a=\{\ell\le R_a:\ell\text{ prime},\ \ell\nmid a+1\},\qquad d_a=|T_a|.
\]

Then

\[
D_a(X)=\#\{q\le X:q\text{ prime},\ A(a,q)=M(a,q)\}
\]

satisfies

\[
D_a(X)\le C_{T_a}(\log X)^{d_a}+O_a((\log X)^{d_a-1}), \tag{12}
\]

and therefore

\[
\frac{D_a(X)}{\pi(X)}=O_a\!\left(\frac{(\log X)^{d_a+1}}{X}\right). \tag{13}
\]

**Proof.** The polynomial-divisor restriction says every common output \(r\) divides \(B_a\), so \(r\le R_a\) and the additive kernel is \(R_a\)-smooth. For \(q>R_a\), the same exclusion argument as in extension 1 shows that the kernel uses only primes in \(T_a\). Thus

\[
D_a(X)\le\pi(R_a)+S_{T_a}(X+a+1).
\]

Apply (*) for (12) and the prime number theorem for (13). The set \(T_a\) is nonempty because \(B_a\equiv-1\pmod{a+1}\), so its greatest prime divisor cannot divide \(a+1\). ∎

## 8. Additive-exponential collisions are confined to a finite region

If

\[
A(p,q)=E_p(q),
\]

then

\[
q\le p, \tag{14}
\]

except at \((p,q)=(2,3)\). If \(p,q\) are odd and \(p+q+1\) is composite, then

\[
p\ge5q+2. \tag{15}
\]

For a triple collision,

\[
q\le\min\!\left(p,\frac{P^+(p^2+p-1)-1}{2}\right). \tag{16}
\]

**Proof.** Outside the exceptional pair, a common output \(r\) satisfies

\[
2q+1\le r\le p+q+1,
\]

which gives (14). If the odd additive kernel \(N=p+q+1\) is composite, then its cofactor after division by \(r=P^+(N)\) is an odd integer at least 3. Therefore

\[
p+q+1=N\ge3r\ge6q+3,
\]

which is (15). For a triple collision, the additive-multiplicative polynomial restriction gives \(r\mid p^2+p-1\), so

\[
2q+1\le r\le P^+(p^2+p-1),
\]

and (16) follows together with (14). The exceptional pair \((2,3)\) is not triple because its multiplicative output is 7 while the additive and exponential outputs are 3. ∎

If \(p\ge3\) and \(p^2+p-1\) is prime, no triple collision can occur at anchor \(p\): the divisor restriction would force the common output to be \(p^2+p-1\), whereas (14) bounds it by \(p+q+1\le2p+1<p^2+p-1\).

## 9. Complete classification of triple collisions with q = 2

For prime \(p\),

\[
A(p,2)=M(p,2)=E_p(2)\quad\Longleftrightarrow\quad p\in\{2,7\}. \tag{17}
\]

The common output is 5.

**Proof.** The existing second-input-2 collision theorem forces any common output to be 5. Direct calculation gives the two solutions: for \(p=2\), the three kernels are all 5; for \(p=7\), the kernels are 10, 15, and 50, all with greatest prime factor 5.

Conversely assume \(p\ne2\). From \(M(2,p)=5\) one obtains \(p\equiv1\pmod3\). Since \(p\) is odd, \(p^2+1\) contains exactly one factor 2 and no factor 3. Thus

\[
p^2+1=2\cdot5^k,\qquad k\ge1.
\]

Modulo 3 forces \(k\) even, hence \(k\ge2\). Modulo 16 then gives \(p^2\equiv1\pmod{16}\).

The additive condition gives

\[
p+3=2^\alpha5^\beta,\qquad \alpha,\beta\ge1,
\]

because 3 does not divide \(p+3\). If \(\beta\ge2\), then \(p\equiv-3\pmod{25}\), so \(p^2+1\equiv10\pmod{25}\), contradicting \(k\ge2\). Hence \(\beta=1\).

Modulo 3, \(5\cdot2^\alpha=p+3\equiv1\), so \(\alpha\) is odd. Since \(p^2\equiv1\pmod{16}\),

\[
p\equiv1,7,9,15\pmod{16}.
\]

In all four cases the 2-adic valuation of \(p+3\) is at most 2. Hence \(\alpha\le2\), and oddness forces \(\alpha=1\). Therefore \(p+3=10\), so \(p=7\). ∎

## 10. Structural separation from the homogeneous additive GPF family

Define

\[
H(p,q)=P^+(p+q).
\]

### Algebraic separation

There is no magma homomorphism from \(H\) into any of \(A,M,E\), and no injective magma homomorphism from any of \(A,M,E\) into \(H\).

**Proof.** For every prime \(p\),

\[
H(p,p)=P^+(2p)=p,
\]

so every element of \(H\) is idempotent. None of \(A,M,E\) has an idempotent because \(p\) divides none of

\[
2p+1,\qquad p^2+1,\qquad p^p+1.
\]

A homomorphism preserves idempotents, which rules out homomorphisms from \(H\) to any of the three new magmas. An injective homomorphism into an idempotent magma would force the source operation to be idempotent, ruling out injective homomorphisms in the reverse direction. ∎

This algebraic statement is Lean-certified on the branch.

### Dynamical separation

For odd prime anchors \(a,c\), every orbit of

\[
H_c(q)=P^+(c+q)
\]

is eventually periodic, while every orbit of \(E_a\) escapes exponentially. More strongly:

- no finite-to-one map \(h:\mathbb P\to\mathbb P\) satisfies \(h\circ E_a=H_c\circ h\);
- no map at all satisfies \(h\circ H_c=E_a\circ h\).

**Proof.** If \(q\) is odd, \(c+q\) is even and composite, so

\[
H_c(q)\le\frac{c+q}{2}.
\]

For \(q=2\), trivially \(H_c(2)\le c+2\). Thus every input above \(c+2\) strictly decreases, while the finite set of primes at most \(c+2\) is forward invariant. Every orbit therefore eventually enters that finite set and is eventually periodic.

An escaping \(E_a\)-orbit contains infinitely many distinct states. A finite-to-one intertwining map cannot send all of them into one finite \(H_c\)-orbit. Conversely, \(H_c(c)=c\); an intertwining map in the reverse direction would send this fixed point to an \(E_a\)-fixed point, but no such fixed point exists for odd \(a\). ∎

---

## Remaining directions

The results above do **not** establish asymptotic equivalences for the actual prime fibers, nor their infinitude, nor a global classification of triple collisions with odd second input. Extensions 1--4 and 7 require a formal weighted-lattice counting layer; the \(\zeta\)-refinements additionally require Möbius inversion. Equation (10) requires formalizing the prime-counting scaling step from the PNT already available in the project.
