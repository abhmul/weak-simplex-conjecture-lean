---
title: "The Regular Simplex Is Optimal for Equal-Energy Gaussian Classification"
subtitle: "A detailed proof through Gaussian maxima, normalized self-convolution, and adaptive tilting"
author: ""
date: ""
lang: en-US
abstract: |
  We prove that among all collections of $n+1$ unit vectors in $\mathbb R^n$, the vertices of a regular simplex maximize the average probability of correct maximum-likelihood decoding in additive standard Gaussian noise, for every signal strength $\lambda>0$. The proof first rewrites the decoding probability as an exponential moment of a Gaussian maximum and then adds one common Gaussian coordinate so that the regular simplex becomes a vector of independent standard Gaussians. The central analytic ingredient is a product inequality for one-dimensional log-concave factors with zero Gaussian barycenter, proved by a sum--difference rotation, a symmetric Gaussian rectangle inequality, dyadic normalized self-convolution, and the central limit theorem. For a centered exponentially tilted half-line, the logarithmic Gaussian mass is a concave function of its endpoint whose derivative is exactly the required tilt. Summing these local log-masses and subtracting the quadratic Gaussian cost of the necessary mean displacement produces a strictly concave potential: its stationarity equation aligns the thresholds, while its value is exactly the logarithmic lower bound needed for stochastic domination. Singular covariances follow by positive-definite approximation.

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

3. **A centered log-concave Gaussian product inequality.** For any Gaussian correlation structure, one-dimensional log-concave factors with zero Gaussian barycenter are positively correlated. The proof uses a sum--difference rotation, a symmetric Gaussian rectangle inequality, dyadic normalized self-convolution, and the central limit theorem.

4. **Centered tilted half-lines and a Gaussian displacement potential.** The centered log-mass of a tilted half-line has derivative equal to its required tilt. For positive-definite $R$, the sum of these local log-masses minus the quadratic cost of the Gaussian mean displacement is a strictly concave potential. Its stationarity equation produces compatible thresholds, and its value gives the desired CDF lower bound. Singular $R$ follows by approximation.

The only non-elementary convex-analytic input is Prékopa's theorem, stated precisely in Section 2. We also use the classical central limit theorem. All other specialized ingredients needed for the main argument are proved below.

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

## 2.4. Positive-definite approximation of a Gaussian covariance

The same approximation will be used repeatedly: for rectangle probabilities, for expectations of bounded log-concave factors, and finally to pass the Gaussian CDF comparison from positive-definite to singular covariance matrices.

> **Lemma 2.1 (positive-definite approximation).** Let $R$ be a $k\times k$ correlation matrix, possibly singular, and let $X\sim N(0,R)$. Let $Z\sim N(0,I_k)$ be independent of $X$. For $0<\varepsilon<1$, define
> \[
> R_\varepsilon=(1-\varepsilon)R+\varepsilon I_k,
> \qquad
> X^{(\varepsilon)}
> =\sqrt{1-\varepsilon}\,X+\sqrt\varepsilon\,Z.
> \]
> Then $R_\varepsilon$ is a positive-definite correlation matrix,
> $X^{(\varepsilon)}\sim N(0,R_\varepsilon)$, and
> $X^{(\varepsilon)}\to X$ almost surely as $\varepsilon\downarrow0$. Consequently:
>
> 1. if $A\subseteq\mathbb R^k$ is Borel and
>    $\mathbb P(X\in\partial A)=0$, then
>    \[
>    \mathbb P(X^{(\varepsilon)}\in A)
>    \longrightarrow
>    \mathbb P(X\in A);
>    \]
> 2. if $F:\mathbb R^k\to\mathbb R$ is bounded and is continuous at $X$ almost surely, then
>    \[
>    \mathbb EF(X^{(\varepsilon)})
>    \longrightarrow
>    \mathbb EF(X).
>    \]

**Proof.** For every nonzero $u\in\mathbb R^k$,
\[
u^{\mathsf T}R_\varepsilon u
=(1-\varepsilon)u^{\mathsf T}Ru+\varepsilon\|u\|^2>0,
\]
so $R_\varepsilon$ is positive definite. Its diagonal entries are $1$, and the covariance formula gives
$X^{(\varepsilon)}\sim N(0,R_\varepsilon)$. The almost-sure convergence is immediate from the displayed coupling.

If $x\notin\partial A$, then $\mathbf1_A$ is continuous at $x$; hence the first conclusion follows from bounded convergence. The second is the dominated convergence theorem. $\square$

## 2.5. Stochastic order and positive exponential moments

For real random variables $U$ and $V$, write $U\le_{\mathrm{st}}V$ when
\[
\mathbb P(U>t)\le\mathbb P(V>t)
\qquad(t\in\mathbb R).
\]

> **Lemma 2.2 (stochastic domination implies exponential-moment domination).** If $U\le_{\mathrm{st}}V$, then, for every $\mu\ge0$,
> \[
> \mathbb E e^{\mu U}
> \le
> \mathbb E e^{\mu V},
> \]
> where the expectations may take the value $+\infty$.

**Proof.** The case $\mu=0$ is equality. If $\mu>0$, then for every $y>0$,
\[
\mathbb P(e^{\mu U}>y)
=
\mathbb P\!\left(U>\frac{\log y}{\mu}\right)
\le
\mathbb P\!\left(V>\frac{\log y}{\mu}\right)
=
\mathbb P(e^{\mu V}>y).
\]
The layer-cake formula for nonnegative random variables now gives
\[
\mathbb E e^{\mu U}
=
\int_0^\infty\mathbb P(e^{\mu U}>y)\,dy
\le
\int_0^\infty\mathbb P(e^{\mu V}>y)\,dy
=
\mathbb E e^{\mu V}.
\]
$\square$

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

Since $R-J/m=\alpha G\succeq0$, it is therefore enough to prove the following stronger statement for every correlation matrix $R$ satisfying $R-J/m\succeq0$:
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

Now allow the covariance matrix to be singular. Apply the positive-definite result to the vectors $V^{(\varepsilon)}$ from Lemma 2.1. For
\[
A=\prod_{i=1}^k[-r_i,r_i],
\]
the boundary $\partial A$ is contained in a finite union of sets of the form $\{|V_i|=r_i\}$, omitting coordinates for which $r_i=\infty$. Every $V_i$ has a continuous standard normal distribution, so $\mathbb P(V\in\partial A)=0$. Lemma 2.1(1) therefore permits passage to the limit and completes the proof. $\square$

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

We now prove the analytic result that will later be applied to exponentially tilted half-lines.

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

## 6.1. Normalization and dyadic normalized self-convolution

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
Thus $\nu_i=h_i\,d\gamma$ is a probability measure with mean zero.

The operation used below is most naturally defined on probability measures. If $Y,Y'$ are independent with common law $\nu$, define the **dyadic normalized self-convolution** of $\nu$ by
\[
T\nu
=
\operatorname{Law}\!\left(\frac{Y+Y'}{\sqrt2}\right).
\]
Equivalently, $T\nu$ is the convolution $\nu*\nu$ followed by dilation by $1/\sqrt2$. Repeated application produces the dyadic normalized sums that appear in the central limit theorem.

Suppose now that $d\nu=h\,d\gamma$. The density of $T\nu$ relative to $\gamma$ can be read off from the Gaussian sum--difference rotation. For every bounded Borel test function $\varphi$,
\[
\begin{aligned}
\int\varphi\,d(T\nu)
&=\iint
  \varphi\!\left(\frac{y+y'}{\sqrt2}\right)
  h(y)h(y')\,d\gamma(y)d\gamma(y')\\
&=\iint
  \varphi(u)
  h\!\left(\frac{u+v}{\sqrt2}\right)
  h\!\left(\frac{u-v}{\sqrt2}\right)
  \,d\gamma(u)d\gamma(v).
\end{aligned}
\]
Here we used the orthogonal change of variables
\[
u=\frac{y+y'}{\sqrt2},
\qquad
v=\frac{y-y'}{\sqrt2},
\]
which preserves $\gamma\otimes\gamma$. Hence
\[
d(T\nu)=(\mathcal Dh)\,d\gamma,
\]
where
\[
(\mathcal Dh)(u)
=
\int_{\mathbb R}
 h\!\left(\frac{u+v}{\sqrt2}\right)
 h\!\left(\frac{u-v}{\sqrt2}\right)
 \,d\gamma(v).
\]
Thus $\mathcal D$ is simply normalized self-convolution written in density coordinates relative to standard Gaussian measure.

We record the properties needed below.

**(a) Boundedness and log-concavity.** If $h$ is bounded and log-concave, then $\mathcal Dh$ is bounded and log-concave. Boundedness is immediate from
\[
\|\mathcal Dh\|_\infty\le\|h\|_\infty^2.
\]
For log-concavity, with respect to Lebesgue measure the integrand is
\[
(u,v)\longmapsto
h\!\left(\frac{u+v}{\sqrt2}\right)
h\!\left(\frac{u-v}{\sqrt2}\right)
\phi(v).
\]
It is jointly log-concave, so Prékopa's theorem applies after integration over $v$.

**(b) Preservation of normalization, centering, and variance.** If $h\,d\gamma$ is the law of $Y$, then $(\mathcal Dh)\,d\gamma$ is the law of $(Y+Y')/\sqrt2$. Consequently,
\[
\int\mathcal Dh\,d\gamma=1.
\]
If $\mathbb EY=0$, then
\[
\int u\,\mathcal Dh(u)\,d\gamma(u)
=
\mathbb E\frac{Y+Y'}{\sqrt2}=0,
\]
and
\[
\operatorname{Var}\!\left(\frac{Y+Y'}{\sqrt2}\right)
=
\operatorname{Var}(Y).
\]
The centering assumption is essential: without it, the mean would be multiplied by $\sqrt2$ at each iteration.

**(c) Iteration.** If $Y_1,Y_2,\dots$ are independent with law $h\,d\gamma$, then, by induction,
\[
(\mathcal D^r h)\,d\gamma
=
\operatorname{Law}\!\left(
2^{-r/2}\sum_{\ell=1}^{2^r}Y_\ell
\right).
\]
This is the probabilistic reason for introducing $\mathcal D$.

## 6.2. The sum--difference step

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
\mathcal Z_R(h_1,\dots,h_k)^2
=
\mathbb E_{U,V}
  \prod_{i=1}^k
  h_i\!\left(\frac{U_i+V_i}{\sqrt2}\right)
  h_i\!\left(\frac{U_i-V_i}{\sqrt2}\right).
\]
Fix $U=u$ and define
\[
g_{i,u_i}(v)
=
 h_i\!\left(\frac{u_i+v}{\sqrt2}\right)
 h_i\!\left(\frac{u_i-v}{\sqrt2}\right).
\]
The difference variable has manufactured the symmetry needed in Corollary 5.2: $g_{i,u_i}$ is even, bounded, and log-concave. Applying that corollary to the conditional expectation over $V$ gives
\[
\begin{aligned}
\mathbb E_V\prod_i g_{i,u_i}(V_i)
&\ge
\prod_i\int g_{i,u_i}(v)\,d\gamma(v)\\
&=\prod_i(\mathcal Dh_i)(u_i).
\end{aligned}
\]
Averaging over $U$ yields
\[
\boxed{
\mathcal Z_R(h_1,\dots,h_k)^2
\ge
\mathcal Z_R(\mathcal Dh_1,\dots,\mathcal Dh_k).
}
\]
The same sum--difference rotation therefore has two roles: conditioning on the average $U$ makes the factors even in the fluctuation $V$, and integrating out $V$ produces normalized self-convolution in the $U$ variable.

## 6.3. Iteration, the central limit theorem, and deficit amplification

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
The inequality from Section 6.2 gives $Z_{r+1}\le Z_r^2$, and hence
\[
Z_r\le Z_0^{2^r}
\qquad(r\ge0).
\]

Let $Y_{i,1},Y_{i,2},\dots$ be independent with law $\nu_i=h_i\,d\gamma$. Section 6.1(c) identifies $h_{i,r}\,d\gamma$ as the law of
\[
S_{i,r}
=
2^{-r/2}\sum_{\ell=1}^{2^r}Y_{i,\ell}.
\]
The law $\nu_i$ has mean zero. Because $h_i$ is bounded, it has moments of every order. Its variance $\sigma_i^2$ is strictly positive: $\nu_i$ is absolutely continuous with respect to Gaussian measure and therefore cannot be a point mass. The central limit theorem gives
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
Fix $L>0$. The function $L_R$ is continuous and strictly positive, so
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

This rules out any initial deficit. Indeed, if $Z_0<1$, then $Z_0^{2^r}\to0$, while $Z_r\le Z_0^{2^r}$; this contradicts the positive lower bound. Therefore $Z_0\ge1$. Undoing the normalization of the $f_i$ proves Theorem 6.1 when $R$ is positive definite.

## 6.4. Passage to singular correlation matrices

Let $R$ now be singular, and use the coupling $X^{(\varepsilon)}\to X$ from Lemma 2.1. The positive-definite case gives
\[
\mathbb E\prod_i f_i(X_i^{(\varepsilon)})
\ge
\prod_i\int f_i\,d\gamma.
\]
A one-dimensional nonzero log-concave function is continuous in the interior of its support and can be discontinuous only at the endpoints of that support. Thus each bounded $f_i$ has at most two discontinuities. Since every $X_i$ is a standard Gaussian, almost surely all $X_i$ are continuity points of $f_i$. The bounded function
\[
F(x)=\prod_i f_i(x_i)
\]
is therefore continuous at $X$ almost surely. Lemma 2.1(2) permits passage to the limit and completes the proof of Theorem 6.1. $\square$

## 6.5. Why the proof works

The centering condition is what prevents the normalized sums in Section 6.1 from developing a drifting mean. The sum--difference rotation handles the dependence in $R$: after conditioning on the average variable, the fluctuation variable makes every one-dimensional factor even, so the symmetric rectangle inequality applies. Iteration then has two competing effects. A hypothetical value $Z_0<1$ is repeatedly squared and driven rapidly toward zero, while normalized self-convolution regularizes each marginal toward a nondegenerate Gaussian law and keeps $Z_r$ bounded away from zero. The contradiction forces $Z_0\ge1$.

# 7. Centered tilted half-lines and their local potential

Theorem 6.1 applies to one-dimensional factors whose Gaussian barycenters vanish. A bare lower half-line cannot satisfy this condition: for every finite $b$,
\[
\int_{-\infty}^b z\,d\gamma(z)=-\phi(b)<0.
\]
Moving the cutoff changes the size of this negative moment but never makes it zero. The useful operation is instead to translate the Gaussian mass inside the half-line. Relative to the standard Gaussian reference measure, such a translation is represented by an exponential tilt:
\[
e^{az}\phi(z)=e^{a^2/2}\phi(z-a).
\]

For $a,b\in\mathbb R$, define the tilted half-line mass
\[
\mathsf Z(a,b)
=
\int_{\mathbb R}e^{az}\mathbf1_{\{z\le b\}}\,d\gamma(z)
=
e^{a^2/2}\Phi(b-a).
\]
The probability measure proportional to
\[
e^{az}\mathbf1_{\{z\le b\}}\,d\gamma(z)
\]
is a $N(a,1)$ law truncated to $(-\infty,b]$. Its mean is
\[
\frac{\partial}{\partial a}\log\mathsf Z(a,b)
=
a-\frac{\phi(b-a)}{\Phi(b-a)}.
\]
Thus centering this measure is equivalent to
\[
a=\frac{\phi(s)}{\Phi(s)},
\qquad
s=b-a.
\]
This is the one-dimensional origin of the functions introduced next.

## 7.1. The centering curve

Let $Z\sim N(0,1)$. For $s\in\mathbb R$, define
\[
r(s)=-\mathbb E[Z\mid Z\le s]
=\frac{\phi(s)}{\Phi(s)},
\qquad
H(s)=s+r(s).
\]
The centered tilted half-lines are exactly
\[
a=r(s),
\qquad
b=H(s)=s+r(s).
\]
Since $r(s)=-\mathbb E[Z\mid Z\le s]$, we also have
\[
H(s)=\mathbb E[s-Z\mid Z\le s]>0.
\]
Indeed, $b-a=s$, and the preceding calculation shows that
\[
z\longmapsto e^{r(s)z}\mathbf1_{\{z\le H(s)\}}
\]
has zero Gaussian barycenter.

We record the properties that allow us to use the endpoint $b$ as the basic variable. Differentiating $r$ gives
\[
\begin{aligned}
r'(s)
&=\frac{\phi'(s)\Phi(s)-\phi(s)\Phi'(s)}{\Phi(s)^2}\\
&=-r(s)(s+r(s))\\
&=-r(s)H(s)<0.
\end{aligned}
\]
A second integration by parts gives
\[
\int_{-\infty}^s z^2\phi(z)\,dz
=
\Phi(s)-s\phi(s),
\]
and therefore
\[
\operatorname{Var}(Z\mid Z\le s)
=
1-sr(s)-r(s)^2.
\]
Since
\[
H'(s)=1+r'(s)=1-sr(s)-r(s)^2,
\]
we obtain the useful identity
\[
\boxed{H'(s)=\operatorname{Var}(Z\mid Z\le s)>0.}
\]
Hence $H$ is strictly increasing. Moreover, conditional on $Z\le s$ we have $-Z\ge -s$, so
\[
r(s)=-\mathbb E[Z\mid Z\le s]\ge -s.
\]
In particular, $r(s)\to\infty$ as $s\to-\infty$.

As $s\to+\infty$, $r(s)\to0$, so $H(s)\to+\infty$. At the other endpoint,
\[
H(s)\Phi(s)
=s\Phi(s)+\phi(s)
=\int_{-\infty}^s\Phi(u)\,du.
\]
Both numerator and denominator in
\[
H(s)=\frac{\int_{-\infty}^s\Phi(u)\,du}{\Phi(s)}
\]
tend to zero as $s\to-\infty$. L'Hôpital's rule gives
\[
\lim_{s\to-\infty}H(s)
=
\lim_{s\to-\infty}\frac{\Phi(s)}{\phi(s)}
=
\lim_{s\to-\infty}\frac1{r(s)}
=0.
\]
Consequently,
\[
H:\mathbb R\longrightarrow(0,\infty)
\]
is a strictly increasing bijection.

For $b>0$, let
\[
\tau(b)=r(H^{-1}(b)).
\]
Then $\tau(b)$ is the unique exponential-tilt parameter for which the half-line ending at $b$ has zero Gaussian barycenter.

## 7.2. The local centered log-mass

Define
\[
\mathcal F(b)
=
\log\mathsf Z(\tau(b),b),
\qquad b>0.
\]
Equivalently, if $b=H(s)$, then
\[
\boxed{
\mathcal F(H(s))
=
\log\Phi(s)+\frac12r(s)^2.
}
\]
Thus $\mathcal F(b)$ is the logarithmic Gaussian mass of the uniquely centered tilted half-line with endpoint $b$.

The decisive identity is
\[
\boxed{\mathcal F'(b)=\tau(b).}
\]
There are two complementary ways to see it. Direct differentiation of the displayed formula gives
\[
\frac{d}{ds}\left(\log\Phi(s)+\frac12r(s)^2\right)
=r(s)H'(s),
\]
so $\mathcal F'(H(s))=r(s)$. Conceptually, it is an envelope identity: along the centered curve,
\[
\frac{\partial}{\partial a}\log\mathsf Z(a,b)=0,
\]
so differentiating the centered value with respect to the endpoint leaves only the direct endpoint derivative. This explains why the derivative of the local log-mass is exactly the tilt required for centering.

Since
\[
\mathcal F''(H(s))
=
\frac{r'(s)}{H'(s)}<0,
\]
the function $\mathcal F$ is strictly increasing and strictly concave. Moreover,
\[
\mathcal F(b)\longrightarrow0
\qquad\text{as }b\to\infty,
\]
so $\mathcal F(b)<0$ for every finite $b>0$.

We also need the behavior at the left endpoint. Put $s=-t$ with $t>0$, and write $Q(t)=\Phi(-t)$. The classical Mills bounds
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
\mathcal F(b)\longrightarrow-\infty
\qquad\text{as }b\downarrow0.
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

# 8. Compatibility as a variational stationarity equation

Fix $c\in\mathbb R$. In this section, assume that $R$ is positive definite and satisfies
\[
R-\frac1mJ\succeq0.
\]
The singular case will be obtained by approximation in Section 10.

The one-dimensional construction assigns to every endpoint vector $b\in(0,\infty)^m$ a unique centered tilt
\[
a_i=\tau(b_i)=\mathcal F'(b_i).
\]
After the multivariate Gaussian change of measure, the same tilt displaces the mean by $Ra$. To recover the common final threshold $c$, we therefore need
\[
b-c\mathbf1=Ra.
\]
The desired parameters must solve the coupled system
\[
\boxed{
a=\nabla\mathcal F_m(b),
\qquad
b-c\mathbf1=Ra,
}
\]
where
\[
\mathcal F_m(b)=\sum_{i=1}^m\mathcal F(b_i).
\]

This system suggests the variational problem directly. The Gaussian cumulant function is
\[
K_R(a)=\frac12a^{\mathsf T}Ra,
\qquad
\nabla K_R(a)=Ra.
\]
Because $R\succ0$, its convex conjugate is
\[
K_R^*(w)=\frac12w^{\mathsf T}R^{-1}w,
\qquad
\nabla K_R^*(w)=R^{-1}w.
\]
Eliminating $a$ from the boxed system gives
\[
\nabla\mathcal F_m(b)
=
\nabla K_R^*(b-c\mathbf1).
\]
This is precisely the stationarity equation of the scalar functional
\[
\boxed{
\Psi_c(b)
=
\sum_{i=1}^m\mathcal F(b_i)
-
\frac12(b-c\mathbf1)^{\mathsf T}R^{-1}(b-c\mathbf1),
\qquad
b\in(0,\infty)^m.
}
\]
The first term is the total local centered log-mass. The second is the Gaussian quadratic cost of producing the required mean displacement $b-c\mathbf1$. Thus the functional is not an auxiliary guess: it is the potential obtained by integrating the two gradient relations that the centered factors and the Gaussian change of measure must satisfy.

## 8.1. Existence, uniqueness, and compatibility

The function $\Psi_c$ is strictly concave. Indeed,
\[
\nabla^2\Psi_c(b)
=
\operatorname{diag}(\mathcal F''(b_1),\dots,\mathcal F''(b_m))
-R^{-1}\prec0.
\]
It also tends to $-\infty$ at every way of escaping its domain. If some coordinate $b_i\downarrow0$, then $\mathcal F(b_i)\to-\infty$. If $\|b\|\to\infty$, then $\mathcal F\le0$ while
\[
-\frac12(b-c\mathbf1)^{\mathsf T}R^{-1}(b-c\mathbf1)
\longrightarrow-\infty.
\]
Every nonempty superlevel set is therefore contained in a compact subset of $(0,\infty)^m$. By continuity, $\Psi_c$ has a maximizer, and strict concavity makes it unique. Denote it by
\[
b_*\in(0,\infty)^m.
\]

At this interior maximizer,
\[
0=\nabla\Psi_c(b_*)
=
(\mathcal F'(b_{*,i}))_{i=1}^m
-R^{-1}(b_*-c\mathbf1).
\]
Define
\[
a_i=\mathcal F'(b_{*,i})=\tau(b_{*,i}),
\qquad
s_i=H^{-1}(b_{*,i}).
\]
Then
\[
b_*-c\mathbf1=Ra,
\]
and, by the definition of $\tau$,
\[
a_i=r(s_i),
\qquad
b_{*,i}=H(s_i)=s_i+a_i.
\]
Hence
\[
\boxed{s+a-Ra=c\mathbf1.}
\]
This proves the existence of the compatible centered tilts. Strict concavity also shows that the compatible endpoint vector $b_*$, and therefore $s$ and $a$, are unique when $R\succ0$.

## 8.2. The variational value is the logarithmic probability bound

At the maximizer, the local identity from Section 7 gives
\[
\mathcal F(b_{*,i})
=
\log\Phi(s_i)+\frac12a_i^2.
\]
Compatibility gives $b_*-c\mathbf1=Ra$, and therefore
\[
\frac12(b_*-c\mathbf1)^{\mathsf T}R^{-1}(b_*-c\mathbf1)
=
\frac12a^{\mathsf T}Ra.
\]
Consequently,
\[
\boxed{
\Psi_c(b_*)
=
\sum_{i=1}^m\log\Phi(s_i)
+
\frac12a^{\mathsf T}(I-R)a.
}
\]
The right-hand side is exactly the logarithm of the lower bound that will emerge after applying Theorem 6.1 and removing the exponential weight. Thus the same functional both enforces threshold compatibility through its stationarity equation and records the final probability bound through its value.

It remains to compare this value with the independent benchmark. We first isolate the consequence of the semidefinite hypothesis that is used here.

> **Lemma 8.1 (rank-one inverse bound).** If $R\succ0$ and $R-J/m\succeq0$, then
> \[
> \mathbf1^{\mathsf T}R^{-1}\mathbf1\le m.
> \]

**Proof.** Conjugating the semidefinite inequality by $R^{-1/2}$ gives
\[
I-
\frac1m(R^{-1/2}\mathbf1)(R^{-1/2}\mathbf1)^{\mathsf T}
\succeq0.
\]
A rank-one matrix $uu^{\mathsf T}/m$ is bounded above by the identity exactly when $\|u\|^2\le m$. Taking $u=R^{-1/2}\mathbf1$ yields the claim. $\square$

Now evaluate $\Psi_c$ at the symmetric trial point
\[
b_0=H(c)\mathbf1=(c+r(c))\mathbf1.
\]
Using the definition of $\mathcal F$ and Lemma 8.1,
\[
\begin{aligned}
\Psi_c(b_0)
&=m\left(\log\Phi(c)+\frac12r(c)^2\right)
-
\frac12r(c)^2\mathbf1^{\mathsf T}R^{-1}\mathbf1\\
&=m\log\Phi(c)
+
\frac12r(c)^2
\left(m-\mathbf1^{\mathsf T}R^{-1}\mathbf1\right)\\
&\ge m\log\Phi(c).
\end{aligned}
\]
Since $b_*$ maximizes $\Psi_c$,
\[
\boxed{
\sum_{i=1}^m\log\Phi(s_i)
+
\frac12a^{\mathsf T}(I-R)a
=
\Psi_c(b_*)
\ge
m\log\Phi(c).
}
\]
For $R=I_m$, the trial point is the maximizer: compatibility reduces to $s=c\mathbf1$, and equality holds throughout.

# 9. The Gaussian CDF comparison for positive-definite $R$

Assume $R\succ0$ and $R-J/m\succeq0$, and retain the vectors $b_*,s,a$ from Section 8. Thus
\[
b_*=s+a,
\qquad
b_*-Ra=c\mathbf1.
\]
For each $i$, define
\[
f_i(z)
=
e^{a_i z}\mathbf1_{\{z\le b_{*,i}\}}.
\]
Since $a_i=r(s_i)>0$, each factor is bounded, nonzero, and log-concave. Completing the square gives
\[
\int f_i\,d\gamma
=
e^{a_i^2/2}\Phi(s_i),
\]
and its Gaussian barycenter is
\[
\begin{aligned}
\int zf_i(z)\,d\gamma(z)
&=e^{a_i^2/2}
\int_{-\infty}^{s_i}(u+a_i)\phi(u)\,du\\
&=e^{a_i^2/2}
\bigl(a_i\Phi(s_i)-\phi(s_i)\bigr)\\
&=0.
\end{aligned}
\]
Theorem 6.1 therefore yields
\[
\mathbb E\left[
 e^{a^{\mathsf T}X}
 \mathbf1_{\{X\le b_*\}}
\right]
\ge
e^{\|a\|^2/2}
\prod_{i=1}^m\Phi(s_i),
\qquad X\sim N(0,R).
\]

We now remove the exponential weight by a finite-dimensional Gaussian change of measure.

> **Lemma 9.1 (Gaussian exponential-tilt identity).** Let $X\sim N(0,R)$, where $R$ may be singular. For every $a\in\mathbb R^m$ and every nonnegative Borel function $F:\mathbb R^m\to[0,\infty]$,
> \[
> \mathbb E\left[
> e^{a^{\mathsf T}X-\frac12a^{\mathsf T}Ra}F(X)
> \right]
> =
> \mathbb E F(X+Ra).
> \]
> Thus $a$ is the exponential-family parameter, while $Ra$ is the actual displacement of the Gaussian mean.

**Proof.** Choose a matrix $T$ and a standard Gaussian vector $Z\sim N(0,I_d)$ such that
\[
X=TZ,
\qquad
TT^{\mathsf T}=R.
\]
Set $\theta=T^{\mathsf T}a$. The standard Gaussian density on $\mathbb R^d$ satisfies
\[
e^{\theta^{\mathsf T}z-\|\theta\|^2/2}\phi_d(z)
=
\phi_d(z-\theta).
\]
Therefore
\[
\begin{aligned}
\mathbb E\left[
 e^{a^{\mathsf T}X-\frac12a^{\mathsf T}Ra}F(X)
\right]
&=
\mathbb E\left[
 e^{\theta^{\mathsf T}Z-\|\theta\|^2/2}F(TZ)
\right]\\
&=\mathbb E F(T(Z+\theta))\\
&=\mathbb E F(X+Ra).
\end{aligned}
\]
$\square$

Apply the lemma with $F=\mathbf1_{\{x\le b_*\}}$. Since $b_*-Ra=c\mathbf1$,
\[
\begin{aligned}
\mathbb P(X\le c\mathbf1)
&=
e^{-a^{\mathsf T}Ra/2}
\mathbb E\left[
e^{a^{\mathsf T}X}\mathbf1_{\{X\le b_*\}}
\right]\\
&\ge
\exp\!\left(\frac12a^{\mathsf T}(I-R)a\right)
\prod_{i=1}^m\Phi(s_i)\\
&=
\exp(\Psi_c(b_*))\\
&\ge
\Phi(c)^m.
\end{aligned}
\]
We have proved
\[
\boxed{
\mathbb P_{N(0,R)}\!\left(\max_iX_i\le c\right)
\ge
\Phi(c)^m
\qquad(c\in\mathbb R)
}
\]
for every positive-definite correlation matrix satisfying $R-J/m\succeq0$.

# 10. Singular covariances and completion of the main theorem

Let $R$ now be an arbitrary correlation matrix satisfying
\[
R-\frac1mJ\succeq0,
\]
possibly singular. For $0<\varepsilon<1$, define
\[
R_\varepsilon=(1-\varepsilon)R+\varepsilon I_m.
\]
Then $R_\varepsilon$ is a positive-definite correlation matrix, and
\[
R_\varepsilon-\frac1mJ
=
(1-\varepsilon)\left(R-\frac1mJ\right)
+
\varepsilon\left(I_m-\frac1mJ\right)
\succeq0.
\]
The positive-definite result therefore gives
\[
\mathbb P_{N(0,R_\varepsilon)}(X\le c\mathbf1)
\ge
\Phi(c)^m.
\]

Use the coupling from Lemma 2.1:
\[
X^{(\varepsilon)}
=
\sqrt{1-\varepsilon}\,X+
\sqrt\varepsilon\,Z,
\]
where $X\sim N(0,R)$ and $Z\sim N(0,I_m)$ are independent. Then
\[
X^{(\varepsilon)}\sim N(0,R_\varepsilon),
\qquad
X^{(\varepsilon)}\longrightarrow X
\quad\text{almost surely}.
\]
The boundary of $(-\infty,c]^m$ is contained in the union of the hyperplanes $\{x_i=c\}$. Every coordinate of $X$ is a standard Gaussian, so this boundary has probability zero. Lemma 2.1 therefore gives
\[
\mathbb P_{N(0,R_\varepsilon)}(X\le c\mathbf1)
\longrightarrow
\mathbb P_{N(0,R)}(X\le c\mathbf1).
\]
Passing to the limit yields
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
\max_iG_i.
\]

Apply Lemma 2.2. For every $\mu>0$,
\[
\mathbb E_{N(0,R)}e^{\mu\max_iX_i}
\le
\mathbb E e^{\mu\max_iG_i}.
\]
The expectation on the right is finite because
\[
e^{\mu\max_iG_i}\le\sum_{i=1}^m e^{\mu G_i}
\]
and $\mathbb E e^{\mu G_i}=e^{\mu^2/2}$.

Returning to the normalization in Section 4,
\[
\psi_\lambda(x_1,\dots,x_m)
=
\frac1m e^{-\mu^2/2}
\mathbb E_{N(0,R)}e^{\mu\max_iX_i},
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
