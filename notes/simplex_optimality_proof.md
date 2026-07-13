---
title: "The Regular Simplex Is Optimal for Equal-Energy Gaussian Classification"
subtitle: "A detailed proof through Gaussian maxima, log-concave doubling, and adaptive tilting"
author: ""
date: ""
lang: en-US
abstract: |
  We prove that among all collections of $n+1$ unit vectors in $\mathbb R^n$, the vertices of a regular simplex maximize the average probability of correct maximum-likelihood decoding in additive standard Gaussian noise, for every signal strength $\lambda>0$. The proof first rewrites the decoding probability as an exponential moment of a Gaussian maximum and then adds one common Gaussian coordinate so that the regular simplex becomes a vector of independent standard Gaussians. The central analytic ingredient is a product inequality for one-dimensional log-concave factors with zero Gaussian barycenter. It is proved by a doubling operation, a symmetric Gaussian rectangle inequality, and the central limit theorem. A strictly concave variational problem built from the inverse Mills ratio then constructs adaptive exponential tilts that convert this product inequality into first-order stochastic domination of the relevant Gaussian maximum by the independent maximum.
---

# 1. Statement of the problem and the main theorem

Let $n\ge 1$, put $m=n+1$, and let
\[
x_1,\dots,x_m\in S^{n-1}\subset \mathbb R^n.
\]
Fix a signal strength $\lambda>0$. A label $I$ is chosen uniformly from $\{1,\dots,m\}$, an independent Gaussian noise vector $Z\sim N(0,I_n)$ is sampled, and one observes
\[
Y=\lambda x_I+Z.
\]
The decoder chooses an index maximizing the score $\langle Y,x_i\rangle$. When several indices tie, we choose any measurable tie-breaking rule that always selects one of the maximizing indices. This convention matters only when some of the $x_i$ coincide; the averaged success probability below is independent of the particular tie-breaking rule.

Define
\[
\psi_\lambda(x_1,\dots,x_m)
=
\frac1m\sum_{j=1}^m
\mathbb P\!\left(
 j=\operatorname*{arg\,max}_{1\le i\le m}\langle Y,x_i\rangle
 \ \middle|\ I=j
\right).
\]

A regular simplex with $m$ vertices is a collection $\Delta_m=\{v_1,\dots,v_m\}\subset S^{m-2}$ satisfying
\[
\langle v_i,v_j\rangle=-\frac1{m-1}
\qquad (i\ne j).
\]
Such a simplex is unique up to an orthogonal transformation and a relabeling of its vertices.

> **Main Theorem.** For every $n\ge1$, every $\lambda>0$, and every $x_1,\dots,x_{n+1}\in S^{n-1}$,
> \[
> \psi_\lambda(x_1,\dots,x_{n+1})
> \le
> \psi_\lambda(\Delta_{n+1}).
> \]
> Thus the regular simplex maximizes the average probability of correct maximum-likelihood decoding in every dimension and at every signal-to-noise ratio.

The proof establishes a stronger stochastic statement. After a Gaussian normalization, the regular simplex becomes a vector of independent standard Gaussians. We prove that the maximum arising from any competing code is stochastically no larger than the maximum of those independent Gaussians.

## 1.1. Roadmap

The argument has four main stages.

1. **Classification becomes a Gaussian maximum.** We rewrite $\psi_\lambda$ as a positive exponential moment of the maximum of a Gaussian score vector.

2. **The regular simplex becomes independence.** By adjoining one common Gaussian coordinate, every code is transformed into a correlation matrix $R$, while the regular simplex is transformed into $R=I_m$.

3. **A centered log-concave Gaussian product inequality.** For any Gaussian correlation structure, one-dimensional log-concave factors with zero Gaussian barycenter are positively correlated. The proof uses a doubling operation, a symmetric Gaussian rectangle inequality, and the central limit theorem.

4. **Adaptive exponential tilting.** For a fixed threshold $c$, a strictly concave finite-dimensional variational problem constructs one tilt per coordinate. These tilts simultaneously center the one-dimensional factors and shift all multivariate thresholds to the same value $c$. The product inequality then yields the desired Gaussian CDF comparison.

The only convex-analytic theorem used without proof is Prékopa's theorem, stated precisely in Section 2. All other ingredients needed for the main argument are proved below.

# 2. Conventions and preliminary facts

## 2.1. Log-concave functions

A function $f:\mathbb R^d\to[0,\infty)$ is **log-concave** if
\[
f((1-\theta)x+\theta y)
\ge
f(x)^{1-\theta}f(y)^\theta
\]
for all $x,y\in\mathbb R^d$ and $\theta\in[0,1]$. Equivalently, one may write $f=e^{-V}$ where $V:\mathbb R^d\to(-\infty,\infty]$ is convex. This extended-valued convention allows $f$ to vanish. In particular, the indicator $\mathbf 1_K$ of a convex set $K$ is log-concave.

We repeatedly use the following elementary closure properties.

- A product of nonnegative log-concave functions is log-concave.
- If $f$ is log-concave and $T$ is affine, then $f\circ T$ is log-concave.
- Every Gaussian density is log-concave.

The nontrivial closure property we need is preservation under marginalization.

> **Prékopa's Theorem.** Let $F:\mathbb R^{p+q}\to[0,\infty)$ be a measurable log-concave function. Suppose that $\int_{\mathbb R^q}F(x,y)\,dy$ is finite for every $x$. Then
> \[
> x\longmapsto \int_{\mathbb R^q}F(x,y)\,dy
> \]
> is log-concave on $\mathbb R^p$.

Two consequences will be important. First, convolving a log-concave function with a Gaussian density produces a log-concave function. Second, if $K$ is convex and $W$ is Gaussian, then the function
\[
t\longmapsto \mathbb P(W+tb\in K)
\]
is log-concave for every fixed vector $b$.

## 2.2. Standard Gaussian notation

We write
\[
\phi(t)=\frac1{\sqrt{2\pi}}e^{-t^2/2},
\qquad
\Phi(t)=\int_{-\infty}^t\phi(u)\,du,
\]
and write $\gamma$ for standard Gaussian measure on $\mathbb R$.

A symmetric positive-semidefinite matrix $R\in\mathbb R^{k\times k}$ with diagonal entries equal to $1$ is called a **correlation matrix**. If $X\sim N(0,R)$, every coordinate $X_i$ is a standard Gaussian, even when $R$ is singular.

## 2.3. A monotone covariance identity

We use the following one-dimensional fact. If $U,U'$ are independent and identically distributed real random variables and $a,b$ are both nondecreasing, or both nonincreasing, then
\[
2\operatorname{Cov}(a(U),b(U))
=
\mathbb E\big[(a(U)-a(U'))(b(U)-b(U'))\big]
\ge0.
\]
The displayed identity follows by expanding the right-hand side.

# 3. From maximum-likelihood decoding to a Gaussian maximum

Let
\[
G=(\langle x_i,x_j\rangle)_{i,j=1}^m
\]
be the Gram matrix of the code. If $Z\sim N(0,I_n)$, define the Gaussian score vector
\[
\xi_i=\langle Z,x_i\rangle,
\qquad
\xi=(\xi_1,\dots,\xi_m).
\]
Then $\xi\sim N(0,G)$ because
\[
\mathbb E[\xi_i\xi_j]
=
\mathbb E\langle Z,x_i\rangle\langle Z,x_j\rangle
=
\langle x_i,x_j\rangle.
\]
Let
\[
M_G=\max_{1\le i\le m}\xi_i.
\]

> **Proposition 3.1 (maximum-likelihood integral identity).**
> \[
> \psi_\lambda(x_1,\dots,x_m)
> =
> \frac{e^{-\lambda^2/2}}m
> \mathbb E e^{\lambda M_G}.
> \]

**Proof.** Let $\phi_n$ be the standard Gaussian density on $\mathbb R^n$. Conditional on $I=i$, the observation $Y$ has density
\[
p_i(y)=\phi_n(y-\lambda x_i).
\]
Because $\|x_i\|=1$,
\[
\begin{aligned}
\phi_n(y-\lambda x_i)
&=(2\pi)^{-n/2}
  \exp\!\left(-\frac12\|y-\lambda x_i\|^2\right)\\
&=\phi_n(y)
  \exp\!\left(\lambda\langle y,x_i\rangle-\frac{\lambda^2}{2}\right).
\end{aligned}
\]
Thus the index maximizing $p_i(y)$ is exactly an index maximizing $\langle y,x_i\rangle$.

Let $D_i$ be the measurable decision region assigned to label $i$. The sets $D_1,\dots,D_m$ form a measurable partition, and for $y\in D_i$, the density $p_i(y)$ equals $\max_j p_j(y)$. Therefore
\[
\begin{aligned}
m\psi_\lambda
&=\sum_{i=1}^m\int_{D_i}p_i(y)\,dy\\
&=\int_{\mathbb R^n}\max_{1\le i\le m}p_i(y)\,dy\\
&=e^{-\lambda^2/2}
  \int_{\mathbb R^n}
  \exp\!\left(\lambda\max_i\langle y,x_i\rangle\right)
  \phi_n(y)\,dy\\
&=e^{-\lambda^2/2}\mathbb E e^{\lambda M_G}.
\end{aligned}
\]
Dividing by $m$ proves the proposition. The same calculation shows that the average success probability is unaffected by the chosen tie-breaking rule. $\square$

# 4. A normalization under which the simplex is independent

Set
\[
\alpha=\frac{m-1}{m},
\qquad
\beta=\frac{m}{m-1}=\alpha^{-1},
\]
and define
\[
R=\alpha G+\frac1mJ,
\qquad
J=\mathbf 1\mathbf 1^{\mathsf T}.
\]
Since $G\succeq0$ and $J\succeq0$, we have $R\succeq0$. Also,
\[
R_{ii}=\alpha G_{ii}+\frac1m
=\frac{m-1}{m}+\frac1m=1.
\]
Hence $R$ is a correlation matrix.

The following probabilistic construction explains this transformation. Let
\[
B\sim N\!\left(0,\frac1{m-1}\right)
\]
be independent of $\xi\sim N(0,G)$, and define
\[
X_i=\sqrt\alpha\,(\xi_i+B).
\]
Then $X=(X_1,\dots,X_m)$ is centered Gaussian and
\[
\operatorname{Cov}(X)
=\alpha\left(G+\frac1{m-1}J\right)
=\alpha G+\frac1mJ
=R.
\]
Let
\[
M_R=\max_iX_i,
\qquad
\mu=\frac\lambda{\sqrt\alpha}
=\lambda\sqrt{\frac m{m-1}}.
\]
Because the same random variable $B$ is added to all coordinates,
\[
M_R=\sqrt\alpha\,(M_G+B),
\qquad
\mu M_R=\lambda(M_G+B).
\]
Using independence of $B$ and $M_G$,
\[
\begin{aligned}
e^{-\mu^2/2}\mathbb E e^{\mu M_R}
&=e^{-\lambda^2/(2\alpha)}
  \mathbb E e^{\lambda M_G}
  \mathbb E e^{\lambda B}\\
&=e^{-\lambda^2m/[2(m-1)]}
  e^{\lambda^2/[2(m-1)]}
  \mathbb E e^{\lambda M_G}\\
&=e^{-\lambda^2/2}\mathbb E e^{\lambda M_G}.
\end{aligned}
\]
Proposition 3.1 therefore becomes
\[
\psi_\lambda(x_1,\dots,x_m)
=
\frac1m e^{-\mu^2/2}
\mathbb E_{N(0,R)}e^{\mu M_R}.
\]

Now consider a regular simplex. Its Gram matrix is
\[
G_\Delta
=
\frac{m}{m-1}\left(I-\frac1mJ\right).
\]
Consequently,
\[
\alpha G_\Delta+\frac1mJ
=
I-\frac1mJ+\frac1mJ
=I.
\]
Thus the regular simplex corresponds exactly to $m$ independent standard Gaussian variables.

It is therefore enough to prove the following stronger statement for every correlation matrix $R$ arising from the normalization above:
\[
\mathbb P_{N(0,R)}\!\left(\max_iX_i\le c\right)
\ge
\Phi(c)^m
\qquad(c\in\mathbb R).
\]
The right-hand side is the distribution function of the maximum of $m$ independent standard Gaussians.

# 5. Symmetric Gaussian rectangles

The product theorem in the next section is built on a symmetric rectangle inequality. We prove the needed form directly.

> **Lemma 5.1 (symmetric Gaussian rectangle inequality).** Let $V=(V_1,\dots,V_k)$ be a centered Gaussian vector with $\operatorname{Var}(V_i)=1$ for every $i$. Then, for all $r_1,\dots,r_k\in[0,\infty]$,
> \[
> \mathbb P\bigl(|V_i|\le r_i\text{ for every }i\bigr)
> \ge
> \prod_{i=1}^k\mathbb P(|Z|\le r_i),
> \]
> where $Z\sim N(0,1)$.

**Proof.** We first suppose that the covariance matrix of $V$ is positive definite and proceed by induction on $k$.

The case $k=1$ is equality. Assume the result is known in dimension $k-1$. Let
\[
A=\{(v_1,\dots,v_{k-1}): |v_i|\le r_i\text{ for }1\le i<k\}.
\]
Conditional on $V_k=t$, the vector $(V_1,\dots,V_{k-1})$ has the form
\[
Y+bt,
\]
where $Y$ is a centered Gaussian vector whose covariance does not depend on $t$, and $b\in\mathbb R^{k-1}$ is fixed. Define
\[
q(t)=\mathbb P(Y+bt\in A).
\]

The set $A$ is symmetric and convex. Since $Y$ and $-Y$ have the same distribution,
\[
q(-t)=\mathbb P(Y-bt\in A)
      =\mathbb P(-Y-bt\in A)
      =\mathbb P(Y+bt\in A)
      =q(t).
\]
Thus $q$ is even.

The function $q$ is log-concave. Indeed, if $\phi_Y$ is the Gaussian density of $Y$, then
\[
q(t)=\int_{\mathbb R^{k-1}}
\mathbf 1_A(y+bt)\phi_Y(y)\,dy.
\]
The integrand is jointly log-concave in $(t,y)$: the indicator is the indicator of a convex set after an affine change of variables, and $\phi_Y$ is log-concave. Prékopa's theorem therefore implies that $q$ is log-concave.

Every even log-concave function on $\mathbb R$ is nonincreasing on $[0,\infty)$. Hence both
\[
s\longmapsto q(s)
\quad\text{and}\quad
s\longmapsto\mathbf 1_{\{s\le r_k\}}
\]
are nonincreasing functions of $s=|V_k|$. By the monotone covariance identity from Section 2.3,
\[
\mathbb E\left[q(V_k)\mathbf 1_{\{|V_k|\le r_k\}}\right]
\ge
\mathbb E q(V_k)\,\mathbb P(|V_k|\le r_k).
\]
The left side is the probability of the full $k$-dimensional rectangle. The first factor on the right is
\[
\mathbb E q(V_k)
=
\mathbb P\bigl(|V_i|\le r_i\text{ for }1\le i<k\bigr).
\]
Since $V_k$ is standard Gaussian, the second factor is $\mathbb P(|Z|\le r_k)$. Applying the induction hypothesis to the first $k-1$ coordinates proves the result.

If the covariance matrix is singular, replace it by
\[
R_\varepsilon=(1-\varepsilon)R+\varepsilon I,
\qquad \varepsilon>0.
\]
The inequality holds for $R_\varepsilon$. The corresponding Gaussian vectors converge in distribution to $V$ as $\varepsilon\downarrow0$, and the boundary of a finite symmetric rectangle has Gaussian probability zero because each coordinate has a continuous standard normal distribution. Passing to the limit completes the proof. $\square$

The rectangle inequality has a useful functional form.

> **Corollary 5.2 (even log-concave factors).** Let $V$ be as in Lemma 5.1. If $g_1,\dots,g_k:\mathbb R\to[0,\infty)$ are bounded, even, and log-concave, then
> \[
> \mathbb E\prod_{i=1}^k g_i(V_i)
> \ge
> \prod_{i=1}^k\int_{\mathbb R}g_i\,d\gamma.
> \]

**Proof.** For each $i$ and each level $s\ge0$, the superlevel set
\[
\{x:g_i(x)>s\}
\]
is a convex symmetric subset of $\mathbb R$, hence is a centered interval, possibly empty or unbounded. The layer-cake formula and Tonelli's theorem give
\[
\begin{aligned}
\mathbb E\prod_i g_i(V_i)
&=\int_{[0,\infty)^k}
  \mathbb P\bigl(g_i(V_i)>s_i\text{ for all }i\bigr)
  \,ds_1\cdots ds_k\\
&\ge\int_{[0,\infty)^k}
  \prod_i\mathbb P(g_i(Z)>s_i)
  \,ds_1\cdots ds_k\\
&=\prod_i\mathbb E g_i(Z).
\end{aligned}
\]
The inequality in the second line is Lemma 5.1. $\square$

# 6. A centered log-concave Gaussian product theorem

We now prove the analytic result that will later be applied to tilted half-lines.

> **Theorem 6.1 (centered log-concave Gaussian product inequality).** Let $R$ be any $k\times k$ correlation matrix, let $X\sim N(0,R)$, and let $f_1,\dots,f_k$ be bounded, nonnegative log-concave functions with positive Gaussian integrals. Assume that each factor has zero Gaussian barycenter:
> \[
> \int_{\mathbb R}x f_i(x)\,d\gamma(x)=0.
> \]
> Then
> \[
> \mathbb E\prod_{i=1}^k f_i(X_i)
> \ge
> \prod_{i=1}^k\int_{\mathbb R}f_i\,d\gamma.
> \]

We divide the proof into several steps.

## 6.1. Normalization and the doubling operator

Normalize each factor by setting
\[
h_i=\frac{f_i}{\int f_i\,d\gamma}.
\]
Then
\[
\int h_i\,d\gamma=1,
\qquad
\int xh_i(x)\,d\gamma(x)=0.
\]
The probability measure $h_i\,d\gamma$ therefore has mean zero.

For a bounded nonnegative function $h$, define its **doubling transform** by
\[
(\mathcal Dh)(u)
=
\int_{\mathbb R}
 h\!\left(\frac{u+v}{\sqrt2}\right)
 h\!\left(\frac{u-v}{\sqrt2}\right)
 \,d\gamma(v).
\]

We record four properties.

**(a) Log-concavity.** If $h$ is log-concave, then $\mathcal Dh$ is log-concave. With respect to Lebesgue measure, the integrand is
\[
(u,v)\longmapsto
h\!\left(\frac{u+v}{\sqrt2}\right)
 h\!\left(\frac{u-v}{\sqrt2}\right)
 \phi(v).
\]
It is jointly log-concave, so Prékopa's theorem applies after integrating over $v$.

**(b) Preservation of mass.** If $\int h\,d\gamma=1$, then
\[
\int\mathcal Dh\,d\gamma=1.
\]
Indeed, the orthogonal change of variables
\[
y=\frac{u+v}{\sqrt2},
\qquad
y'=\frac{u-v}{\sqrt2}
\]
preserves the product Gaussian measure $d\gamma(u)d\gamma(v)$, so
\[
\begin{aligned}
\int\mathcal Dh(u)\,d\gamma(u)
&=\iint
 h\!\left(\frac{u+v}{\sqrt2}\right)
 h\!\left(\frac{u-v}{\sqrt2}\right)
 \,d\gamma(v)d\gamma(u)\\
&=\iint h(y)h(y')\,d\gamma(y)d\gamma(y')=1.
\end{aligned}
\]

**(c) Preservation of the barycenter.** If $\int xh(x)\,d\gamma(x)=0$, then
\[
\int u\,\mathcal Dh(u)\,d\gamma(u)=0.
\]
Under the same orthogonal change of variables, $u=(y+y')/\sqrt2$, and the integral becomes
\[
\frac1{\sqrt2}\iint(y+y')h(y)h(y')\,d\gamma(y)d\gamma(y')=0.
\]

**(d) Probabilistic meaning.** If $Y,Y'$ are independent with common law $h\,d\gamma$, then $\mathcal Dh\,d\gamma$ is the law of
\[
\frac{Y+Y'}{\sqrt2}.
\]
This follows from the same orthogonal change of variables and is the reason for the name ``doubling transform.''

## 6.2. The key doubling inequality

For bounded functions $q_1,\dots,q_k$, define
\[
\mathcal Z_R(q_1,\dots,q_k)
=
\mathbb E_{N(0,R)}\prod_{i=1}^k q_i(X_i).
\]
Let $X,X'$ be independent copies of $N(0,R)$, and put
\[
U=\frac{X+X'}{\sqrt2},
\qquad
V=\frac{X-X'}{\sqrt2}.
\]
Because $(X,X')$ is jointly Gaussian and the transformation is orthogonal in the copy index, $U$ and $V$ are independent, and each has distribution $N(0,R)$.

Therefore
\[
\begin{aligned}
\mathcal Z_R(h_1,\dots,h_k)^2
&=\mathbb E_{U,V}
  \prod_{i=1}^k
  h_i\!\left(\frac{U_i+V_i}{\sqrt2}\right)
  h_i\!\left(\frac{U_i-V_i}{\sqrt2}\right).
\end{aligned}
\]
Fix $U=u$ and define, as a function of one real variable $v$,
\[
g_{i,u_i}(v)
=
 h_i\!\left(\frac{u_i+v}{\sqrt2}\right)
 h_i\!\left(\frac{u_i-v}{\sqrt2}\right).
\]
This function is even, bounded, and log-concave. Corollary 5.2, applied to the conditional expectation over $V$, gives
\[
\begin{aligned}
\mathbb E_V\prod_i g_{i,u_i}(V_i)
&\ge
\prod_i\int g_{i,u_i}(v)\,d\gamma(v)\\
&=\prod_i(\mathcal Dh_i)(u_i).
\end{aligned}
\]
Averaging over $U$ yields the key inequality
\[
\mathcal Z_R(h_1,\dots,h_k)^2
\ge
\mathcal Z_R(\mathcal Dh_1,\dots,\mathcal Dh_k).
\]

## 6.3. Iteration and the central limit theorem

Define recursively
\[
h_{i,0}=h_i,
\qquad
h_{i,r+1}=\mathcal Dh_{i,r},
\]
and write
\[
Z_r=\mathcal Z_R(h_{1,r},\dots,h_{k,r}).
\]
Iterating the doubling inequality gives
\[
Z_0^{2^r}\ge Z_r
\qquad(r\ge0).
\]

Let $\nu_i=h_i\,d\gamma$, and let $Y_{i,1},Y_{i,2},\dots$ be independent random variables with law $\nu_i$. Property (d) of the doubling transform implies that $h_{i,r}\,d\gamma$ is the law of
\[
S_{i,r}
=
2^{-r/2}\sum_{\ell=1}^{2^r}Y_{i,\ell}.
\]
The law $\nu_i$ has mean zero. Because $h_i$ is bounded, all its moments are finite. Its variance $\sigma_i^2$ is strictly positive: $\nu_i$ is absolutely continuous with respect to Gaussian measure and therefore cannot be a point mass. The central limit theorem gives
\[
S_{i,r}\Longrightarrow N(0,\sigma_i^2).
\]

Assume first that $R$ is positive definite. Its density relative to the product standard Gaussian measure $\gamma^{\otimes k}$ is
\[
L_R(x)
=
(\det R)^{-1/2}
\exp\!\left(-\frac12x^{\mathsf T}(R^{-1}-I)x\right).
\]
Fix any $L>0$. The function $L_R$ is continuous and strictly positive, so
\[
c_{R,L}=\min_{x\in[-L,L]^k}L_R(x)>0.
\]
Consequently,
\[
\begin{aligned}
Z_r
&=\int_{\mathbb R^k}L_R(x)
  \prod_i h_{i,r}(x_i)\,d\gamma^{\otimes k}(x)\\
&\ge c_{R,L}
  \prod_i\int_{-L}^Lh_{i,r}(x)\,d\gamma(x)\\
&=c_{R,L}
  \prod_i\mathbb P(|S_{i,r}|\le L).
\end{aligned}
\]
By the central limit theorem, each factor converges to
\[
\mathbb P(|\sigma_iZ|\le L)>0.
\]
Thus
\[
\liminf_{r\to\infty}Z_r>0.
\]

If $Z_0<1$, then $Z_0^{2^r}\to0$, and the inequality $Z_r\le Z_0^{2^r}$ would force $Z_r\to0$, contradicting the positive lower bound. Therefore $Z_0\ge1$. Undoing the normalization of the $f_i$ proves the theorem when $R$ is positive definite.

## 6.4. Singular correlation matrices

For a singular correlation matrix $R$, set
\[
R_\varepsilon=(1-\varepsilon)R+\varepsilon I,
\qquad \varepsilon>0.
\]
This is a positive-definite correlation matrix, so the theorem holds for $R_\varepsilon$.

To pass to the limit, let $X\sim N(0,R)$ and $Z\sim N(0,I)$ be independent, and define
\[
X^{(\varepsilon)}
=
\sqrt{1-\varepsilon}\,X+\sqrt\varepsilon\,Z.
\]
Then $X^{(\varepsilon)}\sim N(0,R_\varepsilon)$ and $X^{(\varepsilon)}\to X$ almost surely.

A bounded one-dimensional log-concave function is continuous in the interior of its support and can be discontinuous only at the two endpoints of that support. Each coordinate $X_i$ has a continuous standard Gaussian distribution, so almost surely $X_i$ is a continuity point of $f_i$. Hence
\[
\prod_i f_i(X_i^{(\varepsilon)})
\longrightarrow
\prod_i f_i(X_i)
\qquad\text{almost surely}.
\]
The product is uniformly bounded, so dominated convergence applies. Letting $\varepsilon\downarrow0$ completes the proof of Theorem 6.1. $\square$

## 6.5. Why the doubling proof works

The centering condition is used only in the central limit step: repeated doubling forms normalized sums without producing a drifting mean. The symmetric rectangle inequality handles the dependence in $R$ after conditioning on the averaged copy $U$. Iteration drives each one-dimensional factor toward a Gaussian fixed point, while the multivariate partition function cannot collapse to zero. This forces its original value to be at least the independent product.

# 7. The inverse Mills map and a concave primitive

The adaptive tilt requires a particular change of variables built from the inverse Mills ratio. Define
\[
r(s)=\frac{\phi(s)}{\Phi(s)},
\qquad
H(s)=s+r(s).
\]

## 7.1. Monotonicity and range of $H$

Differentiating $r$ gives
\[
\begin{aligned}
r'(s)
&=\frac{\phi'(s)\Phi(s)-\phi(s)\Phi'(s)}{\Phi(s)^2}\\
&=\frac{-s\phi(s)\Phi(s)-\phi(s)^2}{\Phi(s)^2}\\
&=-r(s)(s+r(s))\\
&=-r(s)H(s).
\end{aligned}
\]
Also,
\[
H(s)\Phi(s)=s\Phi(s)+\phi(s).
\]
Since
\[
\frac{d}{ds}\bigl(s\Phi(s)+\phi(s)\bigr)=\Phi(s)
\]
and the expression tends to $0$ as $s\to-\infty$, we have
\[
H(s)\Phi(s)=\int_{-\infty}^s\Phi(u)\,du>0.
\]
Thus $H(s)>0$.

For later use, we spell out the truncated-normal calculation. Integration by parts gives
\[
\int_{-\infty}^s z\phi(z)\,dz=-\phi(s)
\]
and
\[
\int_{-\infty}^s z^2\phi(z)\,dz
=
\Phi(s)-s\phi(s).
\]
Therefore a standard Gaussian conditioned on $\{Z\le s\}$ has mean $-r(s)$ and variance
\[
1-sr(s)-r(s)^2.
\]
Consequently,
\[
H'(s)
=1+r'(s)
=1-r(s)H(s)
=1-sr(s)-r(s)^2
>0.
\]
The strict inequality holds because a Gaussian conditioned on a nontrivial half-line is not almost surely constant. Thus $H$ is strictly increasing.

As $s\to+\infty$, $r(s)\to0$, so $H(s)\to+\infty$. As $s\to-\infty$, both $\int_{-\infty}^s\Phi(u)\,du$ and $\Phi(s)$ tend to zero, and l'Hôpital's rule gives
\[
H(s)
=
\frac{\int_{-\infty}^s\Phi(u)\,du}{\Phi(s)}
\longrightarrow
\frac{\Phi(s)}{\phi(s)}
=\frac1{r(s)}
\longrightarrow0.
\]
The last limit also follows from the Mills estimates proved below. Therefore
\[
H:\mathbb R\to(0,\infty)
\]
is a strictly increasing bijection.

## 7.2. Definition and concavity of the primitive

Define $\mathcal F:(0,\infty)\to\mathbb R$ by
\[
\mathcal F(H(s))
=
\log\Phi(s)+\frac12r(s)^2.
\]
This is well-defined because $H$ is bijective.

Differentiating with respect to $s$,
\[
\begin{aligned}
\frac{d}{ds}\left(\log\Phi(s)+\frac12r(s)^2\right)
&=r(s)+r(s)r'(s)\\
&=r(s)\bigl(1-r(s)H(s)\bigr)\\
&=r(s)H'(s).
\end{aligned}
\]
Hence
\[
\mathcal F'(H(s))=r(s)>0.
\]
Differentiating once more,
\[
\mathcal F''(H(s))
=
\frac{r'(s)}{H'(s)}<0.
\]
Thus $\mathcal F$ is strictly increasing and strictly concave.

As $s\to+\infty$, $\Phi(s)\to1$ and $r(s)\to0$, so
\[
\mathcal F(H(s))\to0.
\]
Because $\mathcal F$ is increasing, it follows that
\[
\mathcal F(y)<0
\qquad(y>0).
\]

We also need the behavior at the left endpoint. Put $s=-t$ with $t>0$, and write $Q(t)=\Phi(-t)$. The elementary Mills inequalities
\[
\frac{t}{1+t^2}\phi(t)
\le Q(t)
\le\frac{\phi(t)}t
\]
imply
\[
r(-t)=\frac{\phi(t)}{Q(t)}\le t+\frac1t.
\]
Therefore
\[
\begin{aligned}
\mathcal F(H(-t))
&=\log Q(t)+\frac12r(-t)^2\\
&\le
-\frac{t^2}{2}-\log t-\frac12\log(2\pi)
+\frac12\left(t+\frac1t\right)^2\\
&=1+\frac1{2t^2}-\log t-\frac12\log(2\pi),
\end{aligned}
\]
which tends to $-\infty$. Hence
\[
\mathcal F(y)\to-\infty
\qquad\text{as }y\downarrow0.
\]

For completeness, the upper Mills bound follows from
\[
Q(t)=\int_t^\infty\phi(u)\,du
\le\frac1t\int_t^\infty u\phi(u)\,du
=\frac{\phi(t)}t.
\]
Integration by parts gives
\[
Q(t)=\frac{\phi(t)}t-
\int_t^\infty\frac{\phi(u)}{u^2}\,du
\ge\frac{\phi(t)}t-\frac{Q(t)}{t^2},
\]
which rearranges to the lower Mills bound.

# 8. The adaptive-tilt variational problem

Fix a threshold $c\in\mathbb R$. Recall that
\[
R=\alpha G+\frac1mJ,
\qquad
\alpha=\frac{m-1}{m}.
\]
For $q\in\mathbb R$ and $v\in\mathbb R^n$, define
\[
\mathcal J_c(q,v)
=
\sum_{i=1}^m
\mathcal F\bigl(q+\alpha\langle x_i,v\rangle\bigr)
-
\frac\alpha2\|v\|^2
-
\frac m2(q-c)^2
\]
on the open convex domain
\[
\mathcal D
=
\left\{(q,v):
q+\alpha\langle x_i,v\rangle>0
\text{ for all }i
\right\}.
\]
The point $(1,0)$ belongs to $\mathcal D$, so the domain is nonempty.

## 8.1. Existence and uniqueness of the maximizer

The function $\mathcal J_c$ is strictly concave. Each term involving $\mathcal F$ is concave because $\mathcal F$ is concave and its argument is affine. The negative quadratic term
\[
-\frac\alpha2\|v\|^2-
\frac m2(q-c)^2
\]
is strictly concave.

The function also tends to $-\infty$ at every way of escaping the domain. If a bounded sequence in $\mathcal D$ approaches the boundary, at least one argument of $\mathcal F$ tends to $0$, and that summand tends to $-\infty$. If $\|(q,v)\|\to\infty$, then $\mathcal F\le0$ and the negative quadratic terms tend to $-\infty$.

For a completely formal compactness argument, choose one point $(q_0,v_0)\in\mathcal D$. The superlevel set
\[
\{(q,v)\in\mathcal D:\mathcal J_c(q,v)\ge\mathcal J_c(q_0,v_0)\}
\]
is bounded and stays a positive distance from the boundary of $\mathcal D$. Its closure is therefore a compact subset of $\mathcal D$, on which the continuous function $\mathcal J_c$ attains its maximum. Strict concavity makes this maximizer unique. Denote it by
\[
(q_*,v_*)\in\mathcal D.
\]

## 8.2. The stationarity equations

Set
\[
y_i=q_*+\alpha\langle x_i,v_*\rangle>0.
\]
Because $H$ maps $\mathbb R$ bijectively onto $(0,\infty)$, there is a unique $s_i\in\mathbb R$ such that
\[
y_i=H(s_i).
\]
Define
\[
a_i=r(s_i)=\mathcal F'(y_i)>0.
\]

Differentiating $\mathcal J_c$ with respect to $v$ and using stationarity gives
\[
0
=
\alpha\sum_{i=1}^m a_i x_i-\alpha v_*,
\]
so
\[
v_*=\sum_{i=1}^m a_i x_i.
\]
Differentiating with respect to $q$ gives
\[
0=\sum_{i=1}^m a_i-m(q_*-c),
\]
so
\[
q_*=c+\bar a,
\qquad
\bar a=\frac1m\sum_{i=1}^m a_i.
\]

Let $a=(a_1,\dots,a_m)^{\mathsf T}$. Since $R=\alpha G+J/m$,
\[
\begin{aligned}
(Ra)_i
&=\alpha\sum_{j=1}^m\langle x_i,x_j\rangle a_j+\bar a\\
&=\alpha\left\langle x_i,\sum_{j=1}^m a_jx_j\right\rangle+\bar a\\
&=\alpha\langle x_i,v_*\rangle+\bar a.
\end{aligned}
\]
Therefore
\[
y_i=q_*+\alpha\langle x_i,v_*\rangle
=c+(Ra)_i.
\]
On the other hand, $y_i=H(s_i)=s_i+a_i$. Hence the vector identity
\[
s+a-Ra=c\mathbf 1
\]
holds.

This is the key output of the variational problem: after the Cameron--Martin shift by $Ra$, all coordinate thresholds become equal to $c$.

## 8.3. Lower bound for the variational value

By definition of $\mathcal F$,
\[
\mathcal F(y_i)
=
\log\Phi(s_i)+\frac12a_i^2.
\]
Furthermore,
\[
\begin{aligned}
a^{\mathsf T}Ra
&=\alpha a^{\mathsf T}Ga+
  \frac1m\left(\sum_i a_i\right)^2\\
&=\alpha\left\|\sum_i a_ix_i\right\|^2
  +m\bar a^2\\
&=\alpha\|v_*\|^2+m(q_*-c)^2.
\end{aligned}
\]
It follows that
\[
\mathcal J_c(q_*,v_*)
=
\sum_{i=1}^m\log\Phi(s_i)
+
\frac12a^{\mathsf T}(I-R)a.
\]

Now evaluate $\mathcal J_c$ at the admissible point
\[
q=H(c)=c+r(c),
\qquad
v=0.
\]
Using the definition of $\mathcal F$,
\[
\begin{aligned}
\mathcal J_c(H(c),0)
&=m\mathcal F(H(c))-
  \frac m2r(c)^2\\
&=m\left(\log\Phi(c)+\frac12r(c)^2\right)
  -\frac m2r(c)^2\\
&=m\log\Phi(c).
\end{aligned}
\]
Since $(q_*,v_*)$ is the maximizer,
\[
\sum_{i=1}^m\log\Phi(s_i)
+
\frac12a^{\mathsf T}(I-R)a
\ge
m\log\Phi(c).
\]

# 9. Exponentially tilted half-lines and the Gaussian CDF bound

Let $X\sim N(0,R)$. For each $i$, define
\[
f_i(z)
=
e^{a_i z}\mathbf 1_{\{z\le s_i+a_i\}}.
\]
Because $a_i>0$, the function is bounded: on its support,
\[
e^{a_i z}\le e^{a_i(s_i+a_i)}.
\]
It is nonzero and log-concave because its logarithm is affine on a half-line and equals $-\infty$ outside that half-line.

Completing the square gives its Gaussian mass:
\[
\begin{aligned}
\int f_i(z)\,d\gamma(z)
&=\int_{-\infty}^{s_i+a_i}e^{a_i z}\phi(z)\,dz\\
&=e^{a_i^2/2}
  \int_{-\infty}^{s_i}\phi(u)\,du\\
&=e^{a_i^2/2}\Phi(s_i).
\end{aligned}
\]
Its Gaussian barycenter is
\[
\begin{aligned}
\int zf_i(z)\,d\gamma(z)
&=e^{a_i^2/2}
  \int_{-\infty}^{s_i}(u+a_i)\phi(u)\,du\\
&=e^{a_i^2/2}
  \bigl(a_i\Phi(s_i)-\phi(s_i)\bigr)\\
&=0,
\end{aligned}
\]
because $a_i=r(s_i)=\phi(s_i)/\Phi(s_i)$.

Theorem 6.1 therefore yields
\[
\begin{aligned}
\mathbb E\left[
 e^{a^{\mathsf T}X}
 \mathbf 1_{\{X_i\le s_i+a_i\ \forall i\}}
\right]
&\ge
\prod_{i=1}^m e^{a_i^2/2}\Phi(s_i)\\
&=
e^{\|a\|^2/2}
\prod_{i=1}^m\Phi(s_i).
\end{aligned}
\]

We now use a Gaussian shift identity.

> **Lemma 9.1 (Cameron--Martin shift in finite dimensions).** Let $X\sim N(0,R)$, where $R$ may be singular. For every $a\in\mathbb R^m$ and every Borel set $B\subseteq\mathbb R^m$,
> \[
> \mathbb E\left[e^{a^{\mathsf T}X}\mathbf 1_{\{X\in B\}}\right]
> =
> e^{a^{\mathsf T}Ra/2}
> \mathbb P(X+Ra\in B).
> \]

**Proof.** Choose a matrix $T$ and a standard Gaussian vector $Z$ such that $X=TZ$ and $TT^{\mathsf T}=R$. Then
\[
a^{\mathsf T}X=(T^{\mathsf T}a)^{\mathsf T}Z.
\]
The standard Gaussian density satisfies
\[
e^{b^{\mathsf T}z}\phi_d(z)
=
e^{\|b\|^2/2}\phi_d(z-b).
\]
Applying this with $b=T^{\mathsf T}a$ and changing variables gives
\[
\begin{aligned}
\mathbb E\left[e^{a^{\mathsf T}X}\mathbf 1_{\{X\in B\}}\right]
&=e^{\|T^{\mathsf T}a\|^2/2}
  \mathbb P\bigl(T(Z+T^{\mathsf T}a)\in B\bigr)\\
&=e^{a^{\mathsf T}Ra/2}
  \mathbb P(X+Ra\in B).
\end{aligned}
\]
This proof does not require $R$ to be invertible. $\square$

Apply the lemma to
\[
B=\{x\in\mathbb R^m:x_i\le s_i+a_i\text{ for all }i\}.
\]
We obtain
\[
\begin{aligned}
&\mathbb E\left[
 e^{a^{\mathsf T}X}
 \mathbf 1_{\{X_i\le s_i+a_i\ \forall i\}}
\right]\\
&\qquad=
 e^{a^{\mathsf T}Ra/2}
 \mathbb P(X\le s+a-Ra).
\end{aligned}
\]
The variational identity $s+a-Ra=c\mathbf1$ therefore gives
\[
e^{a^{\mathsf T}Ra/2}
\mathbb P(X_i\le c\text{ for all }i)
\ge
e^{\|a\|^2/2}
\prod_i\Phi(s_i).
\]
The right-hand side is strictly positive, so the probability on the left is positive and taking logarithms is legitimate. We obtain
\[
\log\mathbb P(X_i\le c\text{ for all }i)
\ge
\sum_i\log\Phi(s_i)
+
\frac12a^{\mathsf T}(I-R)a.
\]
The lower bound from Section 8.3 now yields
\[
\log\mathbb P(X_i\le c\text{ for all }i)
\ge
m\log\Phi(c).
\]
Exponentiating,
\[
\boxed{
\mathbb P_{N(0,R)}\!\left(\max_iX_i\le c\right)
\ge
\Phi(c)^m
\qquad(c\in\mathbb R).
}
\]
If $G_1,\dots,G_m$ are independent standard Gaussians, then
\[
\mathbb P\left(\max_iG_i\le c\right)=\Phi(c)^m.
\]
Hence
\[
\max_iX_i
\le_{\mathrm{st}}
\max_iG_i,
\]
where $\le_{\mathrm{st}}$ denotes first-order stochastic domination.

# 10. Completion of the main theorem

For every $\mu>0$, the function $x\mapsto e^{\mu x}$ is increasing. The Gaussian maxima under consideration have finite exponential moments of every order. Therefore stochastic domination, first applied to bounded truncations of $e^{\mu x}$ and then passed to the limit by monotone convergence, implies
\[
\mathbb E_{N(0,R)}e^{\mu\max_iX_i}
\le
\mathbb E e^{\mu\max_iG_i},
\]
where the $G_i$ are independent standard Gaussians.

Returning to the normalization in Section 4,
\[
\psi_\lambda(x_1,\dots,x_m)
=
\frac1m e^{-\mu^2/2}
\mathbb E_{N(0,R)}e^{\mu\max_iX_i}
\]
and therefore
\[
\psi_\lambda(x_1,\dots,x_m)
\le
\frac1m e^{-\mu^2/2}
\mathbb E e^{\mu\max_iG_i}.
\]
The expression on the right is exactly the value associated with the regular simplex, because the regular simplex is transformed into the independent correlation matrix $I_m$. Thus
\[
\psi_\lambda(x_1,\dots,x_m)
\le
\psi_\lambda(\Delta_m).
\]
This proves the Main Theorem. $\square$

# 11. A useful explicit formula for the simplex value

Although it is not needed for the comparison proof, the optimum can be written as a one-dimensional Gaussian integral. Let $G_1,\dots,G_m$ be independent standard Gaussians, let
\[
\overline G=\frac1m\sum_{i=1}^mG_i,
\]
and put
\[
\mu=\lambda\sqrt{\frac m{m-1}}.
\]
A Gaussian score vector with the regular-simplex covariance has the representation
\[
\left(\sqrt{\frac m{m-1}}(G_i-\overline G)\right)_{i=1}^m.
\]
Indeed, its diagonal entries are $1$ and its off-diagonal entries are $-1/(m-1)$.

Condition on label $1$ being transmitted. Correct decoding means that, for every $j\ne1$,
\[
\lambda+
\sqrt{\frac m{m-1}}(G_1-\overline G)
\ge
-\frac\lambda{m-1}+
\sqrt{\frac m{m-1}}(G_j-\overline G).
\]
After canceling $\overline G$ and rearranging, this is equivalent to
\[
G_j\le G_1+\mu
\qquad(2\le j\le m).
\]
Conditioning on $G_1$ therefore gives
\[
\boxed{
\psi_\lambda(\Delta_m)
=
\mathbb E\bigl[\Phi(G_1+\mu)^{m-1}\bigr].
}
\]
In the original notation $m=n+1$, this becomes
\[
\boxed{
\psi_\lambda(\Delta_{n+1})
=
\mathbb E\left[
\Phi\!\left(G+\lambda\sqrt{\frac{n+1}{n}}\right)^n
\right],
\qquad G\sim N(0,1).
}
\]
