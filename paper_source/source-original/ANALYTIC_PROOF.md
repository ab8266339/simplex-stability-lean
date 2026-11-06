# Analytic proof: unique SNR switching and the strict-normal small-shell minimizer

This note gives a self-contained analytic proof of two claims that are not theorems of `paper_main.tex` (27 October 2026): the unique ordering, in the channel parameter, of the three horizontal decoding curvatures, and the exact small-shell minimizer in the open region where the normal curvature is strictly the smallest. The tangential finite-amplitude regime, the crossing set where two curvatures agree, and every global numerical constant of the manuscript are outside the argument.

The abstract comparisons labelled T1, T2, and T3 in `E:\simplex-proof-20261106\brjd\Goals.lean` are used only as named algebraic targets. Their kernel checks are not evidence for the Gaussian identities proved below. Every constant that the argument needs is derived here. No numerical scan is used, and no effective radius \(\rho_0\) is computed.

## 0. Standing notation

Fix an integer \(m\ge 3\), write \(n=m-1\) and \(\alpha=n/m\), and let \(\mathbf 1\in\R^m\) be the all-ones vector. Set \(J=\mathbf 1\mathbf 1^{\mathsf T}\) and \(P=I_m-J/m\). The regular simplex correlation is \(G_\Delta=P/\alpha\). For a symmetric zero-diagonal matrix \(A\) small enough that \(R=I_m+A\succ 0\), write
\[
S=\sum_{i<j}A_{ij},\qquad Q=\sum_{i<j}A_{ij}^2=\frac12\|A\|_F^2,\qquad r_A=A\mathbf 1.
\]
Let \(\phi\) and \(\Phi\) be the standard normal density and distribution function. For \(c\in\R\),
\[
q(c)=\frac{\phi(c)}{\Phi(c)},\qquad h(c)=c+q(c),\qquad \sigma(c)=1-q(c)h(c).
\]
Both \(\phi\) and \(\Phi\) are smooth, and \(\Phi>0\) on \(\R\), so \(q,h,\sigma\) are smooth on \(\R\).

For \(\mu\in\R\) and an integer \(m\ge 3\), the tilted probability with positive continuous density
\[
p_{m,\mu}(c)=\frac{e^{\mu c}\phi(c)^2\Phi(c)^{m-2}}{\displaystyle\int_{\R}e^{\mu s}\phi(s)^2\Phi(s)^{m-2}\,ds}
\]
is well-defined: the integrand is at most a constant times \(\exp(-(s-\mu/2)^2)\). Write
\[
a_m(\mu)=\E_{m,\mu}[h^2],\qquad b_m(\mu)=\E_{m,\mu}[\sigma],\qquad H_m(\mu)=\E_{m,\mu}[h],
\]
and drop the subscript \(m\) when it is fixed. For a channel amplitude \(\lambda>0\) the manuscript’s integrals are the same expectations against the probability proportional to the weight in its formula for \(\omega_\lambda\), with \(\mu=\lambda/\sqrt\alpha\). Consequently the normalized ratios \(A_\lambda/C_\lambda\), \(B_\lambda/C_\lambda\) equal \(a(\mu)\), \(b(\mu)\). The value \(\mu=0\) is the continuous endpoint of this family. It is not a claim about a channel with \(\lambda=0\).

The normalized curvatures, for \(C_\lambda>0\), are
\begin{align*}
L_0(m,a)&=\frac{(m-1)a}{m},&
L_1(m,a,b)&=\frac{a+(m-2)b}{2},&
L_\perp(m)&=\frac{m-1}{2}.
\end{align*}
Section 9 identifies them with \(\Lambda_0/C_\lambda\), \(\Lambda_1/C_\lambda\), and \(\Lambda_\perp/C_\lambda\).

## 1. Scalar differential identities

**Lemma 1.1.** \(q'=-qh\), \(h'=\sigma\), and \(\sigma'=q(h^2-\sigma)\).

*Proof.* Since \(\phi'=-c\phi\),
\[
q'=\frac{\phi'\Phi-\phi^2}{\Phi^2}=-q\Bigl(c+\frac{\phi}{\Phi}\Bigr)=-qh.
\]
Then \(h'=1+q'=1-qh=\sigma\), and
\[
\sigma'=-q'h-qh'=q h\cdot h-q\sigma=q(h^2-\sigma).
\]

**Lemma 1.2.** For every real \(c\), one has \(h(c)>0\) and \(0<\sigma(c)<1\). In particular \(h\) and \(h^2\) are strictly increasing, and \(q\) is strictly decreasing. Also
\[
0<h(c)\le \max(c,0)+\sqrt{2/\pi},
\]
with equality on the right at \(c=0\).

*Proof.* Let \(g\) be standard normal and let \(Y\) be the law of \(c+g\) conditioned on \(c+g>0\). The conditioning event has probability \(\Phi(c)\in(0,1)\), and the conditional law is supported on \((0,\infty)\) with a non-degenerate absolutely continuous distribution, so its mean is positive and its variance is positive and finite. Write \(Z=c+g\), so \(Z\) has density \(\phi(z-c)\) and \(P(Z>0)=\Phi(c)\). The substitution \(u=z-c\) and the identity \((\phi)'=-u\phi\) give
\[
\E[Z\mathbf 1_{Z>0}]=\int_{-c}^{\infty}(u+c)\phi(u)\,du=\phi(c)+c\Phi(c),
\]
because \(\int_{-c}^{\infty}u\phi(u)\,du=\phi(c)\). Dividing by \(\Phi(c)\) produces \(\E[Y]=c+q(c)=h(c)\). For the second moment, \(u^2\phi(u)=\phi(u)-(u\phi(u))'\) and \([u\phi(u)]_{-c}^{\infty}=c\phi(c)\), so \(\int_{-c}^{\infty}u^2\phi=\Phi(c)-c\phi(c)\). Adding \(\int_{-c}^{\infty}(2cu+c^2)\phi=2c\phi(c)+c^2\Phi(c)\) yields
\[
\E[Z^2\mathbf 1_{Z>0}]=\Phi(c)(1+c^2)+c\phi(c),
\]
hence \(\E[Y^2]=1+c^2+cq(c)=1+ch(c)\). Therefore \(\mathrm{Var}(Y)=1+ch-h^2\). The identity \(h=c+q\) turns the right-hand side into \(1-qh=\sigma\). Thus \(h>0\) and \(\sigma>0\). Since \(q>0\) and \(h>0\), one has \(qh>0\), so \(\sigma<1\).

Now \(h'=\sigma>0\), so \(h\) is strictly increasing, and \((h^2)'=2h\sigma>0\). Also \(q'=-qh<0\), so \(q\) is strictly decreasing. Therefore \(h(c)<h(0)\) for \(c<0\) and \(q(c)\le q(0)\) for \(c\ge 0\). The value \(h(0)=q(0)=\phi(0)/\Phi(0)=\sqrt{2/\pi}\) gives the stated bound.

These conclusions do not use a tail expansion.

## 2. The derivative of \(D\) on its zero locus

Define the scalar functions
\[
F(c)=h(c)^2-\sigma(c),\qquad D(c)=\sigma+\sigma^2-(1-\sigma)h^2.
\]
Both are smooth. The chain rule and Lemma 1.1 give, at every \(c\),
\[
F'=2h\sigma-q F.
\]
In particular, on the locus \(F=0\),
\[
F'=2h\sigma>0,
\]
because \(h>0\) and \(\sigma>0\).

For \(D\), use \(q=(1-\sigma)/h\), which is the rearrangement of \(\sigma=1-qh\). Then
\[
\sigma'=\frac{(1-\sigma)(h^2-\sigma)}{h},\qquad (h^2)'=2h\sigma.
\]
Writing \(s=\sigma(c)\) and \(x=h(c)^2\) at a fixed \(c\),
\begin{equation}
\label{eq:Dprime-expr}
D'(c)=\frac{(1-s)(x-s)}{h}\,(1+2s+x)-2hs(1-s).
\end{equation}
This is an identity of smooth functions, obtained by the chain rule, not by differentiating a remainder.

**Lemma 2.1 (the algebraic content of T1).** Let \(h,s\in\R\) satisfy \(0<h\), \(0<s<1\), and
\[
s+s^2-(1-s)h^2=0.
\]
Then \(x=h^2\) equals \(s(1+s)/(1-s)\), and the right-hand side of \eqref{eq:Dprime-expr} equals
\[
\frac{4s^3}{h(1-s)}>0.
\]
Thus, whenever \(D(c)=0\), one has \(D'(c)>0\).

*Proof.* The constraint solves as \(x=s(1+s)/(1-s)\). Then
\[
x-s=\frac{2s^2}{1-s},\qquad \sigma'\text{ coefficient}=\frac{1-s}{h}\cdot\frac{2s^2}{1-s}=\frac{2s^2}{h}.
\]
Substitute \(x\) into \(1+2s+x\):
\[
1+2s+x=\frac{(1+2s)(1-s)+s(1+s)}{1-s}=\frac{1+2s-s^2}{1-s}.
\]
The expression \eqref{eq:Dprime-expr} becomes
\begin{align*}
&\frac{2s^2}{h}\cdot\frac{1+2s-s^2}{1-s}-2hs(1-s)\\
&\qquad=\frac{2s^2(1+2s-s^2)-2h^2 s(1-s)^2}{h(1-s)}.
\end{align*}
The relation \(h^2=s(1+s)/(1-s)\) gives \(h^2(1-s)^2=s(1+s)(1-s)=s(1-s^2)\), so the second numerator term is \(2s^2(1-s^2)\). The numerator collapses to
\[
2s^2\bigl(1+2s-s^2-1+s^2\bigr)=4s^3.
\]
Hence the expression equals \(4s^3/(h(1-s))\). The hypotheses \(h>0\) and \(0<s<1\) make this positive.

Lemma 2.1 is exactly the frozen statement T1. The identification of the left-hand side with \(dD/dc\) is Lemma 1.1 together with \eqref{eq:Dprime-expr}, and that identification is not part of T1.

The same computation with no constraint shows the sign identity used later for the ratio:
\[
\Bigl(\frac{h^2}{\sigma}\Bigr)'=\frac{h\,D}{\sigma^2}.
\]
Indeed, with \(x=h^2\) and \(s=\sigma\),
\[
\Bigl(\frac{x}{s}\Bigr)'=\frac{x's-xs'}{s^2},\qquad x'=2hs,\qquad s'=\frac{(1-s)(x-s)}{h},
\]
and clearing the positive factor \(h\) produces the numerator \(hD\) if and only if
\[
2s^2-(1-s)(x-s)=s+s^2-(1-s)x,
\]
which is an algebraic identity. Thus, wherever \(D>0\), the ratio \(h^2/\sigma\) is strictly increasing. The sign of \(D\) is proved in Section 4, after the tail expansion.

## 3. Laplace expansion of the Mills ratio, without differentiating remainders

For \(t>0\) the left-tail Mills ratio is
\[
M(t)=\frac{\Phi(-t)}{\phi(t)}=\int_0^\infty\exp(-tv-v^2/2)\,dv.
\]
The substitution \(s=tv\) gives the Laplace representation used in the memorandum,
\[
M(t)=t^{-1}\int_0^\infty e^{-s}\exp\bigl(-s^2/(2t^2)\bigr)\,ds.
\]
At \(c=-t\) one has \(q(-t)=1/M(t)\) and \(h(-t)=1/M(t)-t\).

**Lemma 3.1 (explicit Taylor remainder).** Let \(n\ge 1\) and \(t>0\). Then
\[
M(t)=\sum_{k=0}^{n-1}(-1)^k\frac{(2k)!}{k!\,2^k}\,t^{-(2k+1)}+\theta_n(t),
\]
where
\[
|\theta_n(t)|\le\frac{(2n)!}{n!\,2^n\,t^{2n+1}}.
\]
In particular, for \(n=5\),
\[
M(t)=t^{-1}-t^{-3}+3t^{-5}-15t^{-7}+105t^{-9}+\theta_5(t),
\]
with \(|\theta_5(t)|\le 945\,t^{-11}\). The remainder is not differentiated anywhere below.

*Proof.* For \(x\ge 0\) the Lagrange remainder after the terms of degree \(0,\ldots,n-1\) in \(e^{-x}\) has absolute value at most \(x^n/n!\), because it equals \((-1)^n e^{-\xi}x^n/n!\) for some \(\xi\in(0,x)\) and \(e^{-\xi}\le 1\). Insert \(x=s^2/(2t^2)\), integrate against \(e^{-s}\) on \((0,\infty)\), and use \(\int_0^\infty e^{-s}s^{2n}\,ds=(2n)!\). Dividing by \(t\) gives the bound on \(\theta_n\). The coefficient of \(t^{-(2k+1)}\) is \((-1)^k(2k)!/(k!2^k)\). For \(k\le 4\) these coefficients are \(1,-1,3,-15,105\), and the \(n=5\) bound is \(10!/(120\cdot 32)=945\).

Set \(u=t^{-2}\). For every \(t>0\),
\begin{equation}
\label{eq:M-factor}
M(t)=t^{-1}\bigl(1-u+3u^2-15u^3+105u^4+r(t)\bigr),
\end{equation}
where \(|r(t)|\le 945\,u^5\). Write \(a_0(u)=-u+3u^2-15u^3+105u^4\) and \(a(t)=a_0(u)+r(t)\), so the factor in parentheses is \(1+a(t)\).

**Lemma 3.2 (algebraic inversion on a far ray).** There exist a finite \(T_0\ge 1\) and a finite constant \(C_h\) such that for every \(t\ge T_0\),
\begin{equation}
\label{eq:h-exp}
h(-t)=t^{-1}-2t^{-3}+10t^{-5}-74t^{-7}+\rho_h(t),
\qquad |\rho_h(t)|\le C_h\,t^{-9}.
\end{equation}
The coefficient \(-74\) is required later. Stopping the expansion of \(h\) at \(O(t^{-7})\) does not determine the coefficient of \(t^{-6}\) in \(\sigma\).

*Proof.* As \(u\to 0\), \(a_0(u)\to 0\) and \(r(t)\to 0\). Choose a finite \(T_0\ge 1\) such that \(t\ge T_0\) implies both \(|a_0(u)|\le 1/4\) and \(|r(t)|\le 1/4\). Then \(|a(t)|\le 1/2\) and \(|a_0(u)|\le 1/2\), so \(1+a(t)\ge 1/2\) and \(q(-t)=t/(1+a(t))\) is well-defined. In particular
\[
h(-t)=t\Bigl(\frac{1}{1+a(t)}-1\Bigr).
\]
On the compact interval \(0\le u\le T_0^{-2}\) one has \(|a_0(u)|\le 1/2\), so \(g(u)=(1+a_0(u))^{-1}\) is smooth there. The recurrence below computes the Taylor coefficients of \(g\) at \(0\), because it is the Cauchy product for the reciprocal of the polynomial \(1+a_0\). Lagrange's theorem in the variable \(u\), through degree \(4\), then gives a remainder bounded by a constant times \(u^5\): the fifth derivative of \(g\) is continuous on that compact interval. The recurrence \(b_0=1\) and \(b_n=-\sum_{j=1}^n a_j b_{n-j}\) for the coefficients of \((1+a_0)^{-1}\), with \(a_1=-1\), \(a_2=3\), \(a_3=-15\), \(a_4=105\), gives
\begin{align*}
b_1&=1,\\
b_2&=-(-1+3)=-2,\\
b_3&=-(2+3-15)=10,\\
b_4&=-(-10-6-15+105)=-74.
\end{align*}
Thus
\[
(1+a_0)^{-1}=1+u-2u^2+10u^3-74u^4+O(u^5),
\]
where the \(O(u^5)\) on \(t\ge T_0\) is the Lagrange remainder of \(g\). Both \(a_0(u)\) and \(a(t)\) lie in \([-1/2,1/2]\), and so does the segment between them. On that segment the derivative of \((1+z)^{-1}\) has absolute value at most \(4\), so the mean value theorem gives
\[
\bigl|(1+a)^{-1}-(1+a_0)^{-1}\bigr|\le 4|r(t)|\le 3780\,u^5.
\]
Thus the same expansion holds for \((1+a)^{-1}\), with a possibly larger finite constant. Multiplying by \(t\) and subtracting \(t\) produces \eqref{eq:h-exp}. No derivative of \(\rho_h\) is taken.

**Lemma 3.3.** There exist a finite \(T_1\ge T_0\) and finite constants \(C_\sigma,C_F,C_D\) such that for every \(t\ge T_1\),
\begin{align*}
\sigma(-t)&=t^{-2}-6t^{-4}+50t^{-6}+\rho_\sigma(t),
&|\rho_\sigma|&\le C_\sigma t^{-8},\\[4pt]
F(-t)&=2t^{-4}+\rho_F(t),
&|\rho_F|&\le C_F t^{-6},\\[4pt]
D(-t)&=4t^{-6}+\rho_D(t),
&|\rho_D|&\le C_D t^{-8}.
\end{align*}
In particular there exists a finite \(T_*\) such that \(F(-t)>0\) and \(D(-t)>0\) for all \(t\ge T_*\).

*Proof.* Retain \(t\ge T_0\) and write \(H=th(-t)\), so Lemma 3.2 says
\[
H=1-2u+10u^2-74u^3+\tilde\rho,\qquad |\tilde\rho|\le C_h u^4.
\]
Set \(H_1=H-1=-2u+10u^2-74u^3+\tilde\rho\). From \(q=t+h=t(1+uH)\) and \(\sigma=1-qh\),
\[
qh=H+uH^2,\qquad \sigma=1-H-uH^2=-H_1-u-2uH_1-uH_1^2.
\]
Expand, using only products of series and the bound on \(\tilde\rho\). The terms through \(u^3\) are
\begin{align*}
-H_1&=2u-10u^2+74u^3+O(u^4),\\
-2uH_1&=4u^2-20u^3+O(u^4),\\
H_1^2&=4u^2-40u^3+O(u^4),\\
-uH_1^2&=-4u^3+O(u^4).
\end{align*}
Adding and using \(-u\) gives
\[
\sigma=u-6u^2+50u^3+O(u^4).
\]
The summand \(74u^3\) comes from the coefficient \(-74\) in \(h\). It is the reason that coefficient must be kept. The symbol \(O(u^4)\) denotes a remainder bounded by a constant times \(u^4\) for \(t\ge T_0\); the constant exists because it is a finite combination of \(C_h\) and the absolute values of the displayed coefficients. This is the expansion of \(\sigma\).

Next, \(h^2=uH^2=u(1+2H_1+H_1^2)\). Through order \(u^3\),
\[
h^2=u-4u^2+24u^3+O(u^4).
\]
The coefficient \(24\) uses \(h\) only through \(t^{-5}\). Subtracting the expansion of \(\sigma\),
\[
F=h^2-\sigma=2u^2+O(u^3)=2t^{-4}+O(t^{-6}).
\]
The leading coefficient \(2\) requires \(h\) through its \(10t^{-5}\) term, which fixes the coefficient \(-6t^{-4}\) in \(\sigma\). Choose the constant \(C_F\) from this \(O(t^{-6})\).

For \(D\), square the expansion of \(\sigma\):
\[
\sigma^2=u^2-12u^3+O(u^4),
\]
so \(\sigma+\sigma^2=u-5u^2+38u^3+O(u^4)\). Also
\[
(1-\sigma)h^2=u-5u^2+34u^3+O(u^4),
\]
where the coefficient \(34\) is \(24+4+6\), coming from \(h^2\), from \((-\,u)(-4u^2)\), and from \((6u^2)(u)\). Therefore
\[
D=4u^3+O(u^4)=4t^{-6}+O(t^{-8}).
\]
The leading coefficient \(4\) uses the coefficient \(50\) in \(\sigma\), hence uses the coefficient \(-74\) in \(h\). The constant \(C_D\) exists for the same reason as \(C_F\).

Finally \(F(-t)\ge t^{-4}(2-C_F t^{-2})\) for \(t\ge T_0\), and \(D(-t)\ge t^{-6}(4-C_D t^{-2})\) for \(t\ge T_0\). Any
\[
T_*>\max\bigl(T_0,\sqrt{C_F},\sqrt{C_D/4}\bigr)
\]
is a finite cutoff on which both functions are positive. The value of \(T_*\) is not required.

The same algebra gives the next coefficients \(F=2t^{-4}-26t^{-6}+O(t^{-8})\) directly from the displayed expansions through \(u^3\), but the existence argument uses only the leading terms and the order of the remainder.

## 4. First-zero argument

**Lemma 4.1.** Let \(f\in C^1(\R)\). Suppose there is a finite \(c_0\) such that \(f>0\) on \((-\infty,c_0]\), and suppose \(f'(c)>0\) whenever \(f(c)=0\). Then \(f>0\) on \(\R\).

*Proof.* If the set \(E=\{c:f(c)\le 0\}\) is empty, there is nothing to prove. Otherwise \(c_*=\inf E\) is finite and \(c_*>c_0\). Continuity gives \(f(c_*)=0\), while \(f>0\) on \((-\infty,c_*)\). Differentiability gives
\[
f(c_*-\varepsilon)=-\varepsilon f'(c_*)+o(\varepsilon).
\]
The hypothesis \(f'(c_*)>0\) makes the right-hand side negative for small \(\varepsilon>0\), contradicting positivity on the left. The remainder in this one-variable Taylor expansion is the definition of \(f'(c_*)\); it is not an asymptotic remainder of \(M(t)\).

**Theorem 4.2.** The functions \(F\) and \(D\) are positive on all of \(\R\). Consequently \(\sigma'=qF>0\) everywhere, so \(\sigma\) is strictly increasing, and \((h^2/\sigma)'=hD/\sigma^2>0\) everywhere, so \(h^2/\sigma\) is strictly increasing.

*Proof.* Lemma 3.3 supplies a finite left endpoint beyond which \(F(-t)>0\) and \(D(-t)>0\). On every zero of \(F\), Section 2 gives \(F'=2h\sigma>0\). On every zero of \(D\), Lemma 2.1 gives \(D'>0\). Lemma 4.1 applies to both functions. The sign statements for the derivatives of \(\sigma\) and \(h^2/\sigma\) were proved in Sections 1 and 2, conditionally on \(F>0\) and \(D>0\).

Combined with Lemma 1.2, the four scalar maps \(h\), \(h^2\), \(\sigma\), and \(h^2/\sigma\) are strictly increasing on \(\R\).

## 5. Differentiation under the integral and strict covariance

Let \(w_{m,\mu}(c)=e^{\mu c}\phi(c)^2\Phi(c)^{m-2}\) and let \(Z_m(\mu)=\int_{\R}w_{m,\mu}\). For each fixed \(m\) the map \(\mu\mapsto w_{m,\mu}(c)\) is smooth. On any compact \(\mu\)-interval, \(|c|^N w_{m,\mu}(c)\) is dominated by an integrable multiple of \((1+|c|)^N\exp(-(c-\mu_*)^2/2)\) for a fixed \(\mu_*\) at least as large as the interval. The domination is independent of \(\mu\) inside that interval.

**Lemma 5.1.** For every integer \(m\ge 3\) and every real \(\mu\), the normalizing constant \(Z_m\) is smooth and positive, and if \(f:\R\to\R\) is continuous and \(|f(c)|\le C(1+|c|)^N\), then \(\mu\mapsto\E_{m,\mu}[f]\) is smooth and
\[
\frac{d}{d\mu}\E_{m,\mu}[f(c)]=\mathrm{Cov}_{m,\mu}\bigl(f(c),c\bigr).
\]
If in addition \(f\) is strictly increasing, the covariance is strictly positive.

*Proof.* The difference quotient of \(w_{m,\mu}\) in \(\mu\) is \(w_{m,\mu}(c)\cdot c\cdot e^{\theta c}/e^{\mu c}\) for an intermediate \(\theta\), hence is dominated on a neighborhood of any fixed \(\mu\) by an integrable function of the type above. Differentiation under the integral sign is therefore legitimate and gives \(Z_m'(\mu)=\int c\,w_{m,\mu}\). The same domination applies to \(f(c)w_{m,\mu}(c)\) and to \(c f(c)w_{m,\mu}(c)\), so the quotient defining the expectation may be differentiated by the quotient rule. The result is the covariance.

For the strict sign, let \(X,Y\) be independent copies of the law \(p_{m,\mu}\). Then
\[
\mathrm{Cov}(f(X),X)=\frac12\E\bigl[(f(X)-f(Y))(X-Y)\bigr].
\]
The integrand is nonnegative. It is not almost surely zero: the density \(p_{m,\mu}\) is continuous and strictly positive on \(\R\), so \(P(X\neq Y)=1\), and a strictly increasing \(f\) then gives a strictly positive integrand on \(\{X\neq Y\}\). The expectations exist by the polynomial-growth hypothesis and the Gaussian tail of \(p_{m,\mu}\).

**Lemma 5.2.** For each integer \(m\ge 3\), the maps \(a_m\), \(b_m\), \(H_m\), and \(a_m/b_m\) are smooth and strictly increasing on \(\R\). In particular they are strictly increasing on \([0,\infty)\), and \(H_m(\mu)\ge H_m(0)>0\) for \(\mu\ge 0\).

*Proof.* The functions \(h^2\), \(\sigma\), and \(h\) are continuous, strictly increasing, and of polynomial growth by Lemma 1.2 and Theorem 4.2. Lemma 5.1 gives the result for \(a_m\), \(b_m\), and \(H_m\). Strict increase of \(H_m\) yields \(H_m(\mu)\ge H_m(0)\). Positivity of \(h\) yields \(H_m(0)>0\).

For the ratio, let \(Q_{m,\mu}\) be the probability with density proportional to \(\sigma(c)w_{m,\mu}(c)\). The factor \(\sigma(c)\) does not depend on \(\mu\), lies in \((0,1)\), and is continuous and positive, so \(Q_{m,\mu}\) is again a smooth exponential family in \(\mu\) with the same dominating Gaussian tails. Moreover
\[
\E_{Q_{m,\mu}}\Bigl[\frac{h^2}{\sigma}\Bigr]=\frac{\E_{m,\mu}[h^2]}{\E_{m,\mu}[\sigma]}=\frac{a_m(\mu)}{b_m(\mu)}.
\]
Theorem 4.2 says that \(h^2/\sigma\) is strictly increasing. Lemma 3.3 gives \(h(-t)\sim t^{-1}\) and \(\sigma(-t)\sim t^{-2}\), so \(h^2/\sigma\to 1\) as \(c\to-\infty\). For \(c\ge 0\), the same theorem gives \(\sigma(c)\ge\sigma(0)=1-2/\pi>0\), and Lemma 1.2 gives \(h(c)\le c+\sqrt{2/\pi}\). Hence
\[
0<\frac{h(c)^2}{\sigma(c)}\le\frac{(c+\sqrt{2/\pi})^2}{1-2/\pi}
\]
on \([0,\infty)\). The weight of \(Q_{m,\mu}\) is \(\sigma(c)w_{m,\mu}(c)\). Since \(0<\sigma<1\), every integrable dominant used for \(w_{m,\mu}\) dominates the corresponding integrand for \(Q_{m,\mu}\), and differentiation in \(\mu\) still multiplies that weight by \(c\). The covariance argument of Lemma 5.1 therefore applies to \(Q_{m,\mu}\) and gives strict increase in \(\mu\).

**Lemma 5.3 (monotonicity in the number of signals).** Fix \(\mu\in\R\). For every integer \(m\ge 3\),
\[
b_{m+1}(\mu)>b_m(\mu).
\]
The same strict increase holds for \(a_m(\mu)\), \(H_m(\mu)\), and \(a_m(\mu)/b_m(\mu)\).

*Proof.* The un-normalized weight at \(m+1\) is the weight at \(m\) multiplied by \(\Phi(c)\). The function \(\Phi\) is strictly increasing, and \(\sigma\) is strictly increasing. For a positive probability \(P\) with full support on \(\R\) and a bounded, positive, strictly increasing \(g\), the reweighted expectation of a strictly increasing integrable \(f\) satisfies
\[
\frac{\E[fg]}{\E[g]}-\E[f]=\frac{1}{2\E[g]}\E\bigl[(f(X)-f(Y))(g(X)-g(Y))\bigr]>0,
\]
by the same independent-copy argument as in Lemma 5.1. Apply this to \(P=p_{m,\mu}\), \(g=\Phi\), and \(f=\sigma\). The ratio \(a/b\) is the expectation of the strictly increasing function \(h^2/\sigma\) under the \(\sigma\)-reweighted law, and increasing \(m\) multiplies that law by another strictly increasing copy of \(\Phi\). The polynomial-growth integrability is the same Gaussian estimate as before.

## 6. The benchmark \(b_4(0)>1/2\)

Write \(I_4=\int_{\R}\phi^4\) and \(J=\int_{\R}\phi^2\Phi^2\).

**Lemma 6.1.** \(I_4=1/(4\sqrt 2\,\pi^{3/2})\) and
\[
b_4(0)=1-\frac{4I_4}{3J}.
\]

*Proof.* The identity \(\phi(c)^4=(2\pi)^{-2}e^{-2c^2}\) and \(\int e^{-2c^2}\,dc=\sqrt{\pi/2}\) give
\[
I_4=(2\pi)^{-2}\sqrt{\pi/2}=1/(4\sqrt 2\,\pi^{3/2}).
\]
For the expectation, \(\sigma=1-qh\) and \(qh\,\phi^2\Phi^2=c\phi^3\Phi+\phi^4\). Integrate \(c\phi^3\Phi\) by parts. From \((\phi^3)'=-3c\phi^3\) and the vanishing of \(\phi^3\Phi\) at both ends,
\[
\int c\phi^3\Phi=\frac13\int\phi^4.
\]
Hence \(\int qh\,\phi^2\Phi^2=(4/3)I_4\), and dividing by \(J\) produces the formula. This identity is exact; the arcsin evaluation of \(J\) is not used.

**Lemma 6.2.** \(J\ge (3\pi+2)/(24\pi^{3/2})\), and therefore
\[
b_4(0)\ge 1-\frac{4\sqrt 2}{3\pi+2}.
\]

*Proof.* Expand \(\Phi^2=(\Phi-1/2)^2+(\Phi-1/2)+1/4\). The cross term \(\phi^2(\Phi-1/2)\) is an odd integrable function, so its integral vanishes. Also \(\int\phi^2=1/(2\sqrt\pi)\), hence
\[
J=\frac14\int\phi^2+\int\phi^2(\Phi-1/2)^2=\frac{1}{8\sqrt\pi}+\int\phi^2(\Phi-1/2)^2.
\]
Integration by parts, using \((\phi^2)'=-2c\phi^2\) and vanishing boundary terms, gives
\[
\int c\phi^2(\Phi-1/2)=\frac12\int\phi^3.
\]
Cauchy–Schwarz in the form
\[
\Bigl(\int (c\phi)\cdot\bigl(\phi(\Phi-1/2)\bigr)\Bigr)^2
\le\Bigl(\int c^2\phi^2\Bigr)\Bigl(\int\phi^2(\Phi-1/2)^2\Bigr)
\]
therefore yields a lower bound on the second integral. The Gaussian integrals
\[
\int\phi^3=\frac{1}{2\pi\sqrt 3},\qquad \int c^2\phi^2=\frac{1}{4\sqrt\pi}
\]
are elementary. The resulting quotient is \(1/(12\pi^{3/2})\), and
\[
J\ge\frac{1}{8\sqrt\pi}+\frac{1}{12\pi^{3/2}}=\frac{3\pi+2}{24\pi^{3/2}}.
\]
Cauchy–Schwarz is not asserted to be equality. Because \(I_4>0\), replacing \(J\) by this lower bound increases \(4I_4/(3J)\). The arithmetic
\[
\frac{4I_4}{3}\Big/\frac{3\pi+2}{24\pi^{3/2}}=\frac{4\sqrt 2}{3\pi+2}
\]
is the comparison of Lemma 6.1 with Lemma 6.2’s bound.

**Lemma 6.3.** \(\pi>28/9\) and \(\sqrt 2<17/12\). Consequently \(4\sqrt 2/(3\pi+2)<1/2\), and \(b_4(0)>1/2\).

*Proof.* Let \(\theta=\arctan(1/5)\). Then \(0<\theta<\pi/4\), because \(0<1/5<1\) and tangent is increasing on \((0,\pi/2)\). The double-angle formula applies and gives
\[
\tan(2\theta)=\frac{2\cdot(1/5)}{1-(1/5)^2}=\frac{5}{12}.
\]
Thus \(2\theta\in(0,\pi/2)\). Since \(\tan(2\theta)<1\), one has \(2\theta\in(0,\pi/4)\), and the formula applies again:
\[
\tan(4\theta)=\frac{2\cdot(5/12)}{1-(5/12)^2}=\frac{120}{119},
\]
with \(4\theta\in(0,\pi/2)\). Set \(\alpha=4\theta\) and \(\beta=\arctan(1/239)\in(0,\pi/4)\). Then \(\tan\alpha=120/119>1/239=\tan\beta\). Both angles lie in \((0,\pi/2)\) and tangent is increasing there, so \(\alpha>\beta\) and \(\alpha-\beta\in(0,\pi/2)\). Therefore
\begin{align*}
\tan(\alpha-\beta)
&=\frac{120/119-1/239}{1+(120/119)(1/239)}
=\frac{120\cdot 239-119}{119\cdot 239+120}\\
&=\frac{28680-119}{28441+120}
=\frac{28561}{28561}=1.
\end{align*}
The unique angle in \((0,\pi/2)\) with tangent \(1\) is \(\pi/4\), so
\[
\frac\pi 4=4\arctan\frac15-\arctan\frac1{239}.
\]
For every real \(t\), the identity \((1-t^2)(1+t^2)+t^4=1\) rearranges to
\[
\frac{1}{1+t^2}=1-t^2+\frac{t^4}{1+t^2}.
\]
Integrating from \(0\) to \(x>0\) gives
\[
\arctan x=x-\frac{x^3}{3}+\int_0^x\frac{t^4}{1+t^2}\,dt>x-\frac{x^3}{3},
\]
the integrand being positive. In particular
\[
\arctan\frac15>\frac15-\frac{1}{3\cdot 5^3}=\frac{74}{375}.
\]
The same representation gives \(\arctan y<y\) for \(y>0\), because \(1/(1+t^2)<1\). Thus \(\arctan(1/239)<1/239\). Combining these strict bounds with Machin's formula,
\[
\frac\pi 4>4\cdot\frac{74}{375}-\frac{1}{239}=\frac{296}{375}-\frac{1}{239}=\frac{70369}{89625}.
\]
The cross multiplication \(70369\cdot 9-7\cdot 89625=5946>0\) gives \(70369/89625>7/9\), so \(\pi>28/9\). Both arctangent inequalities are strict.

Separately, \((17/12)^2=289/144>288/144=2\), so \(\sqrt 2<17/12\). Hence
\[
8\sqrt 2<8\cdot\frac{17}{12}=\frac{34}{3},\qquad 3\pi+2>3\cdot\frac{28}{9}+2=\frac{34}{3}.
\]
The second inequality is strict, so \(8\sqrt 2<3\pi+2\) and \(4\sqrt 2/(3\pi+2)<1/2\). Lemma 6.2 gives \(b_4(0)\ge 1-4\sqrt 2/(3\pi+2)>1/2\).

**Corollary 6.4.** For every integer \(m\ge 4\) and every \(\mu\ge 0\),
\[
\frac12<b_m(\mu)<1.
\]

*Proof.* The upper bound holds for every \(m\) and \(\mu\) because \(0<\sigma<1\) pointwise and \(p_{m,\mu}\) has full support, so the expectation of \(\sigma\) cannot attain \(1\). The lower bound holds at \((m,\mu)=(4,0)\) by Lemma 6.3. Lemmas 5.2 and 5.3 move the value strictly upward in each variable separately, and the inequality is already strict at the minimal corner.

## 7. Integral identity and the values at \(\mu=0\)

**Lemma 7.1.** For every integer \(m\ge 3\) and every real \(\mu\),
\begin{equation}
\label{eq:identity}
2a_m(\mu)+(m-1)b_m(\mu)=m+\mu H_m(\mu).
\end{equation}

*Proof.* The logarithmic derivative of the un-normalized weight is
\[
\mu-2c+(m-2)q=\mu-2h+mq,
\]
which is the memorandum’s formula \(p'/p=\mu-2h+mq\). Fix \(R>0\). Then
\[
\int_{-R}^{R}(hp_{m,\mu})'=\bigl[hp_{m,\mu}\bigr]_{-R}^{R}.
\]
The bound of Lemma 1.2 and the Gaussian tail of \(p_{m,\mu}\) force the boundary term to \(0\) as \(R\to\infty\). Expanding the derivative,
\[
(hp)'=\sigma p+h(\mu-2h+mq)p.
\]
The resulting integrand is absolutely dominated by an integrable multiple of \((1+c^2)p_{m,\mu}(c)\), because \(0<\sigma<1\), \(qh=1-\sigma\), and \(h\) has linear growth. Passing to the limit,
\[
b+\mu H-2a+m\E[qh]=0.
\]
The identity \(\E[qh]=1-b\) rearranges into \eqref{eq:identity}.

**Lemma 7.2.** Fix an integer \(m\ge 4\). At \(\mu=0\),
\[
a(0)<\frac m2,\qquad \frac{a(0)}{b(0)}<m,\qquad a(0)+(m-2)b(0)<m-1.
\]
All three inequalities are strict.

*Proof.* The identity at \(\mu=0\) is \(2a+(m-1)b=m\), so \(a=[m-(m-1)b]/2\). Since \(b>0\), one has \(a<m/2\). Next
\[
\frac a b=\frac{m}{2b}-\frac{m-1}{2}.
\]
The inequality \(a/b<m\) rearranges to \(b>m/(3m-1)\). For \(m>1\), \(m/(3m-1)<1/2\), and Corollary 6.4 supplies \(b>1/2\). Finally
\[
a+(m-2)b=\frac{m+(m-3)b}{2}.
\]
Comparing with \(m-1\) rearranges to \((m-3)b<m-2\). For \(m=4\) the right side is \(2\) and the left side is \(b<1\). For \(m>4\), \((m-2)/(m-3)=1+1/(m-3)>1>b\). Every comparison is strict.

## 8. Unboundedness and the three crossings

The fine asymptotics \(b\to 1\), \(H/\mu\to 1/2\), and \(a/\mu^2\to 1/4\) are not required for existence. They are recorded optionally in Section 12.

**Lemma 8.1.** For each integer \(m\ge 3\) and every \(\mu\ge 0\),
\[
2a_m(\mu)>1+\mu H_m(0).
\]
In particular \(a_m(\mu)\to+\infty\) as \(\mu\to+\infty\). For \(m=3\), \(\mu H_3(\mu)\ge \mu H_3(0)\), so \(\mu H_3(\mu)\to+\infty\).

*Proof.* By \eqref{eq:identity} and \(b_m(\mu)<1\),
\begin{align*}
2a_m(\mu)&=m+\mu H_m(\mu)-(m-1)b_m(\mu)\\
&>m+\mu H_m(\mu)-(m-1)=1+\mu H_m(\mu).
\end{align*}
Lemma 5.2 gives \(H_m(\mu)\ge H_m(0)>0\), and the displayed bound follows. The right-hand side tends to infinity. For \(m=3\) the same lemma gives the linear lower bound \(\mu H_3(0)\).

**Lemma 8.2 (algebraic content of T2).** Let \(m\ge 4\), \(a>0\), and \(1/2<b<1\). Then
\begin{align*}
a=\frac m2&\Longrightarrow L_0(m,a)=L_\perp(m)\ \text{and}\ L_\perp(m)<L_1(m,a,b),\\[4pt]
a=mb&\Longrightarrow L_0(m,a)=L_1(m,a,b)\ \text{and}\ L_\perp(m)<L_0(m,a),\\[4pt]
\min\bigl(L_0(m,a),L_\perp(m)\bigr)&<L_1(m,a,b).
\end{align*}

*Proof.* If \(a=m/2\), then \(L_0=(m-1)/2=L_\perp\) and
\[
L_1-L_\perp=\frac{m-2}{2}\Bigl(b-\frac12\Bigr)>0.
\]
If \(a=mb\), then \(L_1=(mb+(m-2)b)/2=(m-1)b=L_0\), while
\[
L_\perp-L_0=(m-1)\Bigl(\frac12-b\Bigr)<0.
\]
For the third claim, the same algebra gives the unrestricted identity
\[
L_1-L_0=\frac{m-2}{2m}(mb-a)\qquad(m>2).
\]
Suppose toward a contradiction that \(L_1\le L_0\) and \(L_1\le L_\perp\). The first forces \(a\ge mb\). The second forces \(a+(m-2)b\le m-1\). Adding these,
\[
a+(m-2)b\ge mb+(m-2)b=2(m-1)b>(m-1),
\]
which contradicts the second inequality. The last step is strict because \(b>1/2\).

Lemma 8.2 is exactly the frozen statement T2. It is pure algebra once \(b>1/2\) is known.

**Theorem 8.3 (unique positive crossings for \(m\ge 4\)).** Fix an integer \(m\ge 4\). There exist unique real numbers
\[
0<\mu_{1\perp}(m)<\mu_{0\perp}(m)<\mu_{01}(m)<\infty
\]
such that
\begin{align*}
a(\mu_{1\perp})+(m-2)b(\mu_{1\perp})&=m-1,\\
a(\mu_{0\perp})&=m/2,\\
a(\mu_{01})&=m\,b(\mu_{01}),
\end{align*}
and each equation has no other root in \([0,\infty)\). Equivalently, the three normalized curvatures satisfy
\[
L_1=L_\perp,\qquad L_0=L_\perp,\qquad L_0=L_1
\]
at these three parameters, in that order.

*Proof.* The maps
\[
f_{1\perp}=a+(m-2)b,\qquad f_{0\perp}=a,\qquad f_{01}=a/b
\]
are continuous and strictly increasing on \([0,\infty)\) by Lemma 5.2. Lemma 7.2 says that their values at \(0\) are strictly less than \(m-1\), \(m/2\), and \(m\) respectively. Lemma 8.1 and the bound \(1/2<b<1\) give
\[
f_{0\perp}(\mu)\to\infty,\qquad f_{01}(\mu)\ge a(\mu)\to\infty,\qquad f_{1\perp}(\mu)\ge a(\mu)\to\infty.
\]
The intermediate-value theorem supplies at least one positive root of each equation, and strict increase supplies uniqueness.

Let \(\mu_{0\perp}\) be the unique root of \(a=m/2\). Corollary 6.4 gives \(b(\mu_{0\perp})>1/2\), so \(a(\mu_{0\perp})<m b(\mu_{0\perp})\). Thus \(f_{01}(\mu_{0\perp})<m\), and the unique root \(\mu_{01}\) of \(f_{01}=m\) lies strictly to the right of \(\mu_{0\perp}\). At the same point,
\[
a+(m-2)b=\frac m2+(m-2)b>\frac m2+\frac{m-2}{2}=m-1,
\]
so \(f_{1\perp}(\mu_{0\perp})>m-1\). The unique root \(\mu_{1\perp}\) lies strictly to the left of \(\mu_{0\perp}\).

This deduction is the frozen statement T3, specialized to the three scalar functions just shown to satisfy its hypotheses: continuity on \([0,\infty)\), strict increase of \(a\), of \(a/b\), and of \(a+(m-2)b\), the strict bounds \(0<a\) and \(1/2<b<1\), the limit \(a\to\infty\), and the three strict inequalities at \(\mu=0\). The kernel check of T3 certifies this abstract implication and nothing about \(h\), \(\sigma\), or \(b_4(0)\). The verification of the hypotheses is the content of Sections 4–8.

## 9. Ordering of the decoding curvatures

For \(\lambda>0\) set \(\mu=\lambda/\sqrt\alpha\) and
\[
\omega_\lambda(c)=\frac{\mu e^{-\mu^2/2}}{m}\,e^{\mu c}\phi(c)^2\Phi(c)^{m-2}.
\]
Let \(A_\lambda=\int\omega_\lambda h^2\), \(B_\lambda=\int\omega_\lambda\sigma\), and \(C_\lambda=\int\omega_\lambda\). The change of scale between \(\omega_\lambda\,dc\) and \(p_{m,\mu}\,dc\) is a positive constant, so \(C_\lambda>0\) and
\[
\frac{A_\lambda}{C_\lambda}=a(\mu),\qquad \frac{B_\lambda}{C_\lambda}=b(\mu).
\]
Define
\[
\Lambda_0=\alpha A_\lambda,\qquad
\Lambda_1=\frac{A_\lambda+(m-2)B_\lambda}{2},\qquad
\Lambda_\perp=\frac{m-1}{2}C_\lambda.
\]
Dividing by \(C_\lambda\) produces exactly \(L_0\), \(L_1\), and \(L_\perp\). Equality and strict inequality of the \(\Lambda\)’s are therefore the same as those of the \(L\)’s.

**Theorem 9.1 (ordering).** Fix an integer \(m\ge 4\) and \(\lambda>0\), and let \(\mu=\lambda/\sqrt\alpha\). On the four open intervals determined by Theorem 8.3,
\begin{align*}
0<\mu<\mu_{1\perp}&\Longrightarrow \Lambda_0<\Lambda_1<\Lambda_\perp,\\
\mu_{1\perp}<\mu<\mu_{0\perp}&\Longrightarrow \Lambda_0<\Lambda_\perp<\Lambda_1,\\
\mu_{0\perp}<\mu<\mu_{01}&\Longrightarrow \Lambda_\perp<\Lambda_0<\Lambda_1,\\
\mu>\mu_{01}&\Longrightarrow \Lambda_\perp<\Lambda_1<\Lambda_0.
\end{align*}
At \(\mu_{1\perp}\) one has \(\Lambda_1=\Lambda_\perp\) and \(\Lambda_0\) strictly smaller than both. At \(\mu_{0\perp}\) one has \(\Lambda_0=\Lambda_\perp\) and \(\Lambda_1\) strictly larger than both. At \(\mu_{01}\) one has \(\Lambda_0=\Lambda_1\) and \(\Lambda_\perp\) strictly smaller than both. The corresponding thresholds in the variable \(\lambda\) are \(\sqrt\alpha\) times the thresholds in \(\mu\).

*Proof.* Strict increase of \(a\), of \(a+(m-2)b\), and of \(a/b\) converts each root into a sign change of \(\Lambda_1-\Lambda_\perp\), of \(\Lambda_0-\Lambda_\perp\), and of \(\Lambda_0-\Lambda_1\). The order of the roots forbids every other permutation. Lemma 8.2 is the endpoint comparison: when \(a=m/2\), \(b>1/2\) forces \(\Lambda_\perp<\Lambda_1\), and when \(a=mb\), the same bound forces \(\Lambda_\perp<\Lambda_0\). The relation \(\lambda=\mu\sqrt\alpha\) is the definition \(\mu=\lambda/\sqrt\alpha\).

The geometric reading of \(\Lambda_0,\Lambda_1,\Lambda_\perp\) as the quadratic coefficients of the decoding deficit follows from the full covariance expansion in Lemma 11.2 and the horizontal metric in the manuscript; Lemma 11.6 computes the corresponding shell-constrained Hessian gaps. Theorem 9.1 itself is a statement about the three explicit integrals.

## 10. The case \(m=3\)

For \(m=3\) the summand \(\mathcal H_0\) is absent. The identity \eqref{eq:identity} becomes \(2a+2b=3+\mu H_3(\mu)\), so
\[
\frac{\Lambda_1}{C_\lambda}=\frac{a+b}{2}=\frac{3+\mu H_3(\mu)}{4},\qquad \frac{\Lambda_\perp}{C_\lambda}=1.
\]
Thus \(\Lambda_1<\Lambda_\perp\), \(\Lambda_1=\Lambda_\perp\), or \(\Lambda_1>\Lambda_\perp\) according as \(\mu H_3(\mu)<1\), \(=1\), or \(>1\).

**Theorem 10.1.** The function \(\mu\mapsto\mu H_3(\mu)\) is continuous and strictly increasing from \([0,\infty)\) onto \([0,\infty)\). It has a unique positive root \(\mu_*(3)\) of the equation \(\mu H_3(\mu)=1\). For \(0<\mu<\mu_*\) the in-plane coefficient is strictly smaller; for \(\mu>\mu_*\) the normal coefficient is strictly smaller; at \(\mu_*\) they agree.

*Proof.* Lemma 5.1 gives \(H_3'(\mu)=\mathrm{Cov}(h,c)>0\). Hence
\[
\frac{d}{d\mu}\bigl(\mu H_3(\mu)\bigr)=H_3(\mu)+\mu H_3'(\mu)>0
\]
for every \(\mu\ge 0\), the value \(H_3(\mu)\) being positive. The function vanishes at \(0\). Lemma 8.1 sends it to infinity. The intermediate-value theorem and strict increase give a unique positive root, and the sign chart is the sentence above.

The frozen T3 does not cover \(m=3\), because its hypothesis begins at \(m\ge 4\). Theorem 10.1 is a separate one-function argument.

## 11. The strict-normal small-shell minimizer

Throughout this section, \(m\ge 3\) is an integer, \(d\ge m\) is an integer, and \(\lambda>0\). Let \(\mu=\lambda/\sqrt\alpha\). Assume the normal coefficient is strictly smaller than every in-plane coefficient that exists:
\begin{equation}
\label{eq:gap}
\begin{aligned}
m\ge 4&\Longrightarrow \mu>\mu_{0\perp}(m),\\
m=3&\Longrightarrow \mu>\mu_*(3).
\end{aligned}
\end{equation}
Equivalently, \(\Lambda_\perp<\Lambda_0\) whenever \(\mathcal H_0\) is present, and \(\Lambda_\perp<\Lambda_1\) in every case. The common value \(\Lambda_0=\Lambda_\perp\) is excluded: the restricted Hessian used below is degenerate there.

### 11.1. Decoding deficit as a smooth function of a free covariance

For unit signals \(x_1,\ldots,x_m\) in \(\R^d\) with Gram matrix \(G\), the maximum-likelihood success probability is
\[
\Pc(G;\lambda)=\frac{e^{-\lambda^2/2}}{m}\,\E\exp(\lambda\max_i\xi_i),\qquad \xi\sim N(0,G).
\]
The deficit against the simplex is \(\delta_\lambda(G)=\Pc(G_\Delta;\lambda)-\Pc(G;\lambda)\). If \(R=\alpha G+J/m\) and an auxiliary standard normal scalar \(B\) of variance \(1/n\) is used to form \(X_i'=\sqrt\alpha\,(\xi_i+B)\), the vector \(X'\) has covariance \(R\), and
\[
\E e^{\mu\max_i X_i'}=e^{\lambda^2/(2n)}\E e^{\lambda\max_i\xi_i}.
\]
The prefactors match for the simplex and for \(G\), and
\[
\delta_\lambda(G)=\frac{e^{-\mu^2/2}}{m}\Bigl(\E_{I_m}e^{\mu\max_i Z_i}-\E_R e^{\mu\max_i X_i}\Bigr).
\]
The right-hand side is defined for every symmetric \(R\) near \(I_m\) with \(R\succeq I_m/2\), whether or not \(R-J/m\) is positive semidefinite. Call this extension \(\mathcal F(R)\). It agrees with \(\delta_\lambda\) on every correlation matrix.

**Lemma 11.1.** On a neighborhood of \(A=0\) in the space of symmetric zero-diagonal matrices, \(R=I_m+A\) stays positive definite and \(\mathcal F(I_m+A)\) is a smooth function of the entries of \(A\). Its third derivatives are bounded on a smaller closed neighborhood. Consequently Taylor’s theorem supplies a constant \(C\), depending only on \(m\) and \(\mu\), such that the remainder after the degree-\(2\) Taylor polynomial is at most \(C\|A\|_F^3\) throughout that neighborhood.

*Proof.* Restrict to a convex neighborhood of the identity whose closure satisfies \(I_m/2\preceq R\preceq 2I_m\). Let \(p_R(x)\) be the Gaussian density. For each multi-index \(\beta\) in covariance coordinates with \(|\beta|=k\), differentiating the density gives \(\partial_R^\beta p_R(x)=P_{\beta,R}(x)p_R(x)\), where \(P_{\beta,R}\) has degree at most \(2k\) and its coefficients are uniformly bounded on this compact covariance set. Therefore
\[
|\partial_R^\beta p_R(x)|\le C_\beta(1+\|x\|^{2k})e^{-\|x\|^2/4}.
\]
Multiplying this bound by \(e^{\mu\max_i x_i}\le e^{\mu\|x\|}\) preserves integrability. Differentiation under the integral is justified for every fixed order. Integrating the density Taylor remainder against this common dominant gives the asserted \(O(\|A\|_F^3)\) remainder for the expectation, uniformly in a smaller convex covariance neighborhood. This also proves smoothness and local boundedness of all required derivatives.

The remainder in Lemma 11.1 is the Taylor remainder of a function of finitely many real variables. It is not obtained by differentiating an unspecified big-O symbol.

### 11.2. Quadratic form at independence

**Lemma 11.2.** For symmetric zero-diagonal \(A\) sufficiently small,
\begin{equation}
\label{eq:quad}
\begin{aligned}
\mathcal F(I+A)
&=S\,C_\lambda+\frac{A_\lambda}{4}\|A\|_F^2
-\frac{\|A\mathbf 1\|^2}{2}(C_\lambda-B_\lambda)\\
&\qquad+\frac{S^2}{2}\int_{\R}\omega_\lambda(c)\,q(c)^2\,dc
+O(\|A\|_F^3).
\end{aligned}
\end{equation}
The cubic remainder is the one in Lemma 11.1, after the quadratic terms have been identified. The coefficient of \(S^2\) is finite: Lemma 1.2 gives \(0<q(c)\le |c|+\sqrt{2/\pi}\), and \(q^2\) times the Gaussian weight defining \(\omega_\lambda\) is integrable.

*Proof.* It is enough to identify the first and second derivatives of the orthant function
\[
F_R(c)=\Pp(X_i\le c\text{ for all }i),\qquad X\sim N(0,R),
\]
at \(R=I_m\), and then integrate. The representation
\[
\E e^{\mu\max Z_i}-\E_R e^{\mu\max X_i}=\mu\int_{\R}e^{\mu c}\bigl(F_R(c)-\Phi(c)^m\bigr)\,dc
\]
holds by integration by parts in the distribution of the maximum. It can be differentiated through order two at the identity. To justify this directly, each positive-order covariance derivative of the Gaussian density has total integral zero. For \(c\ge0\), its integral over the orthant is therefore minus its integral over the complement, which is contained in \(\{\|x\|\ge c\}\). For \(c\le0\), the orthant itself is contained in \(\{\|x\|\ge |c|\}\). The bounds in Lemma 11.1 imply a uniform bound \(C_k(1+|c|^{N_k})e^{-c^2/8}\) on these orthant derivatives. This bound remains integrable after multiplication by \(e^{\mu c}\), and justifies differentiation of the displayed identity under the integral. We use the orthant expansion only to identify derivatives at the identity; the uniform cubic remainder for the integrated expectation comes separately from Lemma 11.1.

Since \(\operatorname{tr} A=0\),
\[
\log(I+A)=A-\frac12 A^2+O(\|A\|^3),\qquad
\det(I+A)^{-1/2}=\exp\bigl(\tfrac14\|A\|_F^2+O(\|A\|^3)\bigr).
\]
The expansion \((I+A)^{-1}=I-A+A^2+O(\|A\|^3)\) gives
\[
-\frac12 x^{\mathsf T}\bigl((I+A)^{-1}-I\bigr)x
=\frac12 x^{\mathsf T}Ax-\frac12 x^{\mathsf T}A^2x+O(\|A\|^3\|x\|^2).
\]
The explicit density Taylor coefficients are
\[
p_{I+A}(x)=p_I(x)\left[1+\frac12x^{\mathsf T}Ax+\frac14\|A\|_F^2+\frac18(x^{\mathsf T}Ax)^2-\frac12x^{\mathsf T}A^2x\right]+R_A(x),
\]
where Lemma 11.1 gives the uniform bound
\[
|R_A(x)|\le C\|A\|_F^3(1+\|x\|^6)e^{-\|x\|^2/4}.
\]
This is a bound on the density remainder, not a uniform polynomial bound on the density ratio.

Because \(\operatorname{diag} A=0\),
\[
\frac12 x^{\mathsf T}Ax=\sum_{i<j}A_{ij}x_ix_j.
\]
Write \(k=\phi^2\Phi^{m-2}\) and
\[
\alpha_0=\Phi(c),\qquad
\alpha_1=\int_{-\infty}^c x\phi(x)\,dx=-\phi(c),\qquad
\alpha_2=\int_{-\infty}^c x^2\phi(x)\,dx.
\]
The identity \((x\phi)'=(1-x^2)\phi\), together with \(x\phi(x)\to 0\) as \(x\to-\infty\), yields \(\alpha_2=\alpha_0-c\phi(c)\). Integrating the linear term over \((-\infty,c]^m\) produces \(kS\).

For the quadratic monomials, \(\|A\|_F^2=2Q\) contributes \(\tfrac12 A_{ij}^2\) to the coefficient of each square. The square of \(\sum A_{ij}x_ix_j\) contributes \(\tfrac12 x_i^2x_j^2\), and the diagonal terms of \(-\tfrac12 x^{\mathsf T}A^2x\) contribute \(-\tfrac12(x_i^2+x_j^2)\). Integrating over the orthant, the coefficient of \(A_{ij}^2\) becomes
\[
\frac12\bigl(\alpha_0^2+\alpha_2^2-2\alpha_0\alpha_2\bigr)\Phi^{m-2}
=\frac12(\alpha_0-\alpha_2)^2\Phi^{m-2}
=\frac12 c^2 k.
\]
An adjacent product \(A_{ij}A_{ik}\) has ratio coefficient \(x_i^2 x_j x_k-x_j x_k\), and its integral is
\[
\alpha_1^2(\alpha_2-\alpha_0)\Phi^{m-3}=-c\,q\,k.
\]
A disjoint product \(A_{ij}A_{k\ell}\) has ratio coefficient \(x_ix_jx_kx_\ell\) and integral \(q^2 k\). The edge sums
\[
\|r_A\|^2=2Q+2\sum_{\mathrm{adjacent}}A_{ij}A_{ik},
\qquad
S^2=Q+2\sum_{\mathrm{adjacent}}A_{ij}A_{ik}+2\sum_{\mathrm{disjoint}}A_{ij}A_{k\ell}
\]
rearrange to
\[
\sum_{\mathrm{adjacent}}A_{ij}A_{ik}=\frac12\|r_A\|^2-Q,
\qquad
\sum_{\mathrm{disjoint}}A_{ij}A_{k\ell}=\frac{S^2+Q-\|r_A\|^2}{2}.
\]
Adding the three contributions and dividing by \(k\) produces the coefficient of \(Q\),
\[
\frac12 c^2+cq+\frac12 q^2=\frac12 h^2,
\]
and the coefficient of \(\|r_A\|^2\),
\[
-\frac12 cq-\frac12 q^2=-\frac12 qh.
\]
Thus
\[
\frac{F_{I+A}(c)-\Phi(c)^m}{k}
=S+\frac{h^2}{2}Q-\frac{qh}{2}\|r_A\|^2+\frac{q^2}{2}S^2+O_c(\|A\|_F^3).
\]
Here \((h^2/2)Q=h^2\|A\|_F^2/4\). For each fixed \(c\), the remainder constant in this normalized display may depend on \(c\). Multiply the explicitly displayed normalized Taylor coefficients by \(\omega_\lambda(c)=\mu e^{-\mu^2/2}m^{-1}e^{\mu c}k(c)\), and then integrate; the justified derivative interchange above identifies the integrated coefficients, and Lemma 11.1 independently supplies the integrated cubic remainder. The integral of the coefficient of \(S\) is \(C_\lambda\), the integral of the coefficient of \(\|A\|_F^2/4\) is \(A_\lambda\), and
\[
\int\omega_\lambda\,qh=\int\omega_\lambda(1-\sigma)=C_\lambda-B_\lambda.
\]
The integral of the coefficient of \(S^2\) is \(\tfrac12\int\omega_\lambda q^2\). This is \eqref{eq:quad}. On the zero-distance surface of Lemma 11.4 one has \(S=O(\|D\|_F^2)\), so the \(S^2\) term is \(O(\|D\|_F^4)\) and does not enter the Hessian.

### 11.3. Trace coordinates on a shell

Let \(H=\mathbf 1^\perp\), a Euclidean space of dimension \(n\). Every symmetric zero-diagonal \(m\times m\) matrix \(A\) is uniquely of the form \(A=A(C)\) for a symmetric operator \(C\) on \(H\), where \(\widehat C\) is the extension of \(C\) by zero on \(\operatorname{span}\{\mathbf 1\}\) and
\[
A(C)=\widehat C-\frac12\Bigl(\mathbf 1\,\operatorname{diag}(\widehat C)^{\mathsf T}+\operatorname{diag}(\widehat C)\,\mathbf 1^{\mathsf T}\Bigr).
\]
The inverse operation is \(C=(PAP)|_H\). Indeed, for \(x,y\in H\) one has \(y^{\mathsf T}A(C)x=y^{\mathsf T}\widehat C x\). Also \(\mathbf 1^{\mathsf T}A(C)\mathbf 1=-m\operatorname{tr} C\). Since the diagonal of \(A(C)\) vanishes, \(\mathbf 1^{\mathsf T}A(C)\mathbf 1=2S\), and therefore
\[
S=-\frac m2\operatorname{tr} C.
\]
In particular \(\operatorname{tr} C=0\) if and only if \(A(C)\) lies in the trace-zero summand
\[
\mathcal H=\{B=B^{\mathsf T}:\operatorname{diag} B=0,\ \mathbf 1^{\mathsf T}B\mathbf 1=0\}.
\]

**Lemma 11.3 (exact configuration distance).** Let \(G\) be the Gram matrix of a unit-column configuration in dimension \(d\ge n\), let \(A=\alpha(G-G_\Delta)\), and let \(C=(PAP)|_H\). If \(I_H+C\succeq 0\), then
\begin{equation}
\label{eq:dp-exact}
d_P(X,\Delta)^2=2m-\frac{2}{\alpha}\operatorname{tr}\sqrt{I_H+C},
\end{equation}
where the square root is the positive-semidefinite one. Equivalently, if \(\lambda_1,\ldots,\lambda_n\) are the eigenvalues of \(PGP\) on \(H\), then
\[
d_P^2=\frac{\|\textstyle\sum_i x_i\|^2}{m}+\sum_{j=1}^n\bigl(\sqrt{\lambda_j}-\alpha^{-1/2}\bigr)^2,
\]
and \(\lambda_j=(1+\theta_j)/\alpha\) with \(\theta_j\) the eigenvalues of \(C\).

*Proof.* The Gram \(G_\Delta=V^{\mathsf T}V=P/\alpha\) has eigenvalue \(1/\alpha\) on \(H\) and eigenvalue \(0\) on \(\operatorname{span}\{\mathbf 1\}\). The nonzero eigenvalues of \(VV^{\mathsf T}\) are the same, and the image of \(V\) is \(E=\operatorname{span}\{v_i\}\), so \(VV^{\mathsf T}=\alpha^{-1}I_E\). Therefore
\[
(XV^{\mathsf T})(XV^{\mathsf T})^{\mathsf T}=X(P/\alpha)X^{\mathsf T}.
\]
The nonzero eigenvalues of \(XMX^{\mathsf T}\) equal those of \(M^{1/2}GM^{1/2}\) for the positive-semidefinite square root. Taking \(M=P/\alpha\), whose square root is \(P/\sqrt\alpha\), gives the eigenvalues of \((PGP)/\alpha\). On \(H\) these are \(\lambda_j/\alpha\). The singular values of \(XV^{\mathsf T}\) are \(\sqrt{\lambda_j/\alpha}\). If \(M_*=L\Sigma Q^{\mathsf T}\) is a singular-value decomposition and \(U\in O(d)\), then
\[
\operatorname{tr}(U^{\mathsf T}M_*)=\sum_i R_{ii}\sigma_i,
\qquad R=Q^{\mathsf T}U^{\mathsf T}L\in O(d).
\]
Each diagonal entry of an orthogonal matrix is at most \(1\), and each \(\sigma_i\ge 0\), so the trace is at most \(\sum\sigma_i\). The choice \(U=LQ^{\mathsf T}\) attains the bound. Hence
\[
\max_{U\in O(d)}\operatorname{tr}(U^{\mathsf T}XV^{\mathsf T})=\alpha^{-1/2}\sum_j\sqrt{\lambda_j},
\]
and \(d_P^2=2m-2\alpha^{-1/2}\sum\sqrt{\lambda_j}\). The relation \(PGP|_H=(I_H+C)/\alpha\) gives \(\lambda_j=(1+\theta_j)/\alpha\), so
\[
\alpha^{-1/2}\sum\sqrt{\lambda_j}=\alpha^{-1}\operatorname{tr}\sqrt{I_H+C}.
\]
Multiplying by \(2\) produces \eqref{eq:dp-exact}. For the eigenvalue form, \(\sum_j\lambda_j=\operatorname{tr}(PGP)=m-\|\sum_i x_i\|^2/m\) and \(n/\alpha=m\), and expanding \(\sum(\sqrt{\lambda_j}-\alpha^{-1/2})^2\) reproduces the same expression. For nonrealizable \(C\), the trace expression \(2m-2\alpha^{-1}\operatorname{tr}\sqrt{I_H+C}\) defines a scalar extension that is smooth when \(I_H+C\succ0\). No actual configuration distance or real barycenter is asserted there. This scalar extension, together with the extended loss \(\mathcal F\), is what is used in the ambient trace-free coordinates below.

**Lemma 11.4 (shell coordinate).** Let \(\tau\ge 0\) be small and let \(D\) be a trace-free symmetric operator on \(H\), small in Frobenius norm. The equation
\[
\operatorname{tr}\sqrt{I_H+sI_H+D}=n\Bigl(1-\frac{\tau}{2m}\Bigr)
\]
has a unique small smooth solution \(s=s(D,\tau)\), defined for \(\|D\|_F\) and \(|\tau|\) sufficiently small. One has \(s(0,0)=0\) and
\[
\partial_s\big|_{(0,0)}\operatorname{tr}\sqrt{I_H+sI_H+D}=\frac n2>0.
\]
Along \(\tau=0\),
\begin{equation}
\label{eq:s-exp}
s(D,0)=\frac{\|D\|_F^2}{4n}+O(\|D\|_F^3).
\end{equation}
The corresponding sum of off-diagonal entries is
\begin{equation}
\label{eq:S-exp}
S=-\frac m8\|D\|_F^2+O(\|D\|_F^3).
\end{equation}

*Proof.* The map \((s,D)\mapsto\sqrt{(1+s)I+D}\) is smooth for small \((s,D)\) because the positive-definite square root is smooth. At the origin the derivative of the trace in \(s\) equals \(\tfrac12\operatorname{tr}(I_H)=n/2\) by the Daleckii–Krein formula, or by the scalar expansion \(\sqrt{1+s}=1+s/2+O(s^2)\). The implicit-function theorem supplies \(s(D,\tau)\). The power series
\[
\sqrt{I+H}=I+\frac H2-\frac{H^2}{8}+O(\|H\|^3)
\]
with \(H=sI+D\) and \(\operatorname{tr} D=0\), inserted into the constraint at \(\tau=0\), yields \(s=\|D\|_F^2/(4n)+O(\|D\|_F^3)\) once one knows a priori that \(s=O(\|D\|_F^2)\), which follows from the implicit-function expansion because the first derivative in \(D\) of the constraint at the origin vanishes on the trace-free slice. For the pure trace \(C=sI_H\) one has \(\operatorname{tr} C=ns\), so the identity \(S=-(m/2)\operatorname{tr} C\) becomes \(S=-(mn/2)s\). Substituting \eqref{eq:s-exp} gives \eqref{eq:S-exp}. The cubic symbols are Taylor remainders of the smooth map \(s(D,0)\).

The constraint is exactly \(d_P^2=\tau\) for every realizable configuration, by Lemma 11.3. Solving it for the trace part \(s\) does not require the configuration to be realizable.

### 11.4. Permutation stationarity

Let \(F_\tau(D)=\mathcal F\bigl(I+A(s(D,\tau)I_H+D)\bigr)\) on the neighborhood produced by Lemma 11.4.

**Lemma 11.5.** For every sufficiently small \(\tau\), the origin is a critical point of \(F_\tau\).

*Proof.* A permutation matrix preserves \(\mathbf 1\), hence preserves \(H\), and acts on trace-free symmetric operators by conjugation. The spectrum of \(sI+D\) is conjugation-invariant, so the implicit-function solution satisfies \(s(\Pi D\Pi^{\mathsf T},\tau)=s(D,\tau)\). The maximum of coordinates has the same law for \(N(0,R)\) and for its coordinate permutation, so \(F_\tau(\Pi D\Pi^{\mathsf T})=F_\tau(D)\).

Fix a trace-free \(D\). The directional derivative of \(F_\tau\) at \(0\) along \(D\) equals the directional derivative along every conjugate \(\Pi D\Pi^{\mathsf T}\), hence equals the directional derivative along the group average \(\overline D\). Conjugation-invariant symmetric matrices are linear combinations of \(I\) and \(J\). Those that preserve \(H\) and annihilate \(\mathbf 1\) are scalar multiples of \(I_H\). The trace-free condition forces the scalar to vanish, so \(\overline D=0\). The directional derivative along \(0\) is \(0\). Every direction has therefore derivative \(0\).

### 11.5. The Hessian at the origin

Define
\begin{align*}
\mathcal H_0&=\{B\in\mathcal H:B\mathbf 1=0\},\\
\mathcal H_1&=\{B\in\mathcal H:B_{ij}=a_i+a_j\text{ for }i\neq j,\ \sum_i a_i=0\}.
\end{align*}
For \(m=3\), \(\mathcal H_0=\{0\}\). Given \(B\in\mathcal H\), the vector \(B\mathbf 1\) is orthogonal to \(\mathbf 1\). For \(m\ge 3\) set \(a=(B\mathbf 1)/(m-2)\), so \(\sum a_i=0\), and let \(B_1\) be the matrix with off-diagonal entries \(a_i+a_j\). Then
\[
(B_1\mathbf 1)_i=\sum_{j\neq i}(a_i+a_j)=(m-2)a_i,
\]
hence \((B-B_1)\mathbf 1=0\). The diagonal of \(B_1\) vanishes and \(\mathbf 1^{\mathsf T}B_1\mathbf 1=0\), so \(B_0=B-B_1\) lies in \(\mathcal H_0\). The sum is direct. It is Frobenius-orthogonal because
\[
\sum_{i\neq j}(B_0)_{ij}(a_i+a_j)=2a^{\mathsf T}(B_0\mathbf 1)=0.
\]
The parameter \(a\) runs through a space of dimension \(m-1\). Hence \(\dim\mathcal H_1=m-1\) and
\[
\dim\mathcal H_0=\frac{m(m-1)}{2}-1-(m-1)=\frac{m(m-3)}{2}.
\]
On \(\mathcal H_1\), the hypothesis \(\sum a_i=0\) gives
\begin{align*}
\|B\|_F^2
&=\sum_{i\neq j}(a_i+a_j)^2
=2(m-1)\|a\|^2+2\bigl((\textstyle\sum_i a_i)^2-\|a\|^2\bigr)
=2(m-2)\|a\|^2.
\end{align*}
The same hypothesis gives \((B\mathbf 1)_i=\sum_{j\neq i}(a_i+a_j)=(m-2)a_i\), so
\[
\|B\mathbf 1\|^2=(m-2)^2\|a\|^2=\frac{m-2}{2}\|B\|_F^2.
\]
Write \(B=B_0+B_1\) and
\[
E_0=\frac{\|B_0\|_F^2}{4\alpha},\qquad E_1=\frac{\|B_1\|_F^2}{2}.
\]
Thus \(\|B\|_F^2=4\alpha E_0+2E_1\) and \(\|B\mathbf 1\|^2=(m-2)E_1\).

**Lemma 11.6.** Let \(B=A(D)\) for trace-free \(D\). Then
\[
\|D\|_F^2=\|B\|_F^2-\frac{2\|B\mathbf 1\|^2}{m},
\]
and the map \(D\mapsto B\) is a linear isomorphism from the trace-free symmetric operators on \(H\) onto \(\mathcal H\). Along \(\tau=0\),
\begin{equation}
\label{eq:hessian-form}
F_0(D)=(\Lambda_0-\Lambda_\perp)E_0+(\Lambda_1-\Lambda_\perp)E_1+O(\|D\|_F^3),
\end{equation}
where a missing summand is omitted when its space is \(\{0\}\). Under the gap hypothesis \eqref{eq:gap} the quadratic form on the right is positive definite.

*Proof.* Let \(u=\operatorname{diag}\widehat D\). Trace-freedom gives \(\sum u_i=0\), so \(u\perp\mathbf 1\) and \(\widehat D\mathbf 1=0\). Then \(A(D)\mathbf 1=-(m/2)u\), and
\[
\|A(D)\mathbf 1\|^2=\frac{m^2}{4}\|u\|^2.
\]
The correction \(R=\tfrac12(\mathbf 1 u^{\mathsf T}+u\mathbf 1^{\mathsf T})\) is Frobenius-orthogonal to \(\widehat D\) because \(\widehat D\mathbf 1=0\) and \(\mathbf 1^{\mathsf T}u=0\). Also \(\|\mathbf 1 u^{\mathsf T}\|_F^2=\|u\mathbf 1^{\mathsf T}\|_F^2=m\|u\|^2\) and the cross term is \((\mathbf 1^{\mathsf T}u)^2=0\), so \(\|R\|_F^2=(m/2)\|u\|^2\). Therefore
\[
\|A(D)\|_F^2=\|D\|_F^2+\frac m2\|u\|^2.
\]
Eliminating \(u\) produces \(\|D\|_F^2=\|B\|_F^2-2\|B\mathbf 1\|^2/m\). Dimensions agree:
\[
\dim\mathcal H=\frac{m(m-1)}{2}-1=\dim\{D\in\operatorname{Sym}(H):\operatorname{tr} D=0\},
\]
and the map is linear and injective because \(A(D)=0\) implies \(D=0\). It is therefore an isomorphism, and it identifies the trace-free slice with \(\mathcal H\).

Now apply \eqref{eq:quad} to \(A=A(sI+D)\) at \(\tau=0\). Lemma 11.4 gives \(s=O(\|D\|_F^2)\) and \(S=-(m/8)\|D\|_F^2+O(\|D\|_F^3)\). The pure-trace piece \(A(sI)\) is \(O(\|D\|_F^2)\), so it changes \(\|A\|_F^2\) and \(\|A\mathbf 1\|^2\) only by \(O(\|D\|_F^3)\) relative to the same quantities formed from \(B=A(D)\). The term \(S^2\) in \eqref{eq:quad} is \(O(\|D\|_F^4)\). Substituting \(\|D\|_F^2=\|B\|_F^2-2\|B\mathbf 1\|^2/m\) into the linear term \(S C_\lambda\) and using \(\|B\|_F^2=4\alpha E_0+2E_1\) and \(\|B\mathbf 1\|^2=(m-2)E_1\) produces, after cancellation,
\[
(\Lambda_0-\Lambda_\perp)E_0+(\Lambda_1-\Lambda_\perp)E_1.
\]
The cancellation may be checked on the two pure modes, which span the orthogonal decomposition. If \(B\in\mathcal H_0\), then \(E_1=0\), \(\|B\mathbf 1\|=0\), and \(\|B\|_F^2=4\alpha E_0\), and the quadratic polynomial collapses to \(\alpha E_0(A_\lambda-m C_\lambda/2)=(\Lambda_0-\Lambda_\perp)E_0\) because \(\alpha m=m-1\). If \(B\in\mathcal H_1\), then \(E_0=0\), \(\|B\|_F^2=2E_1\), and \(\|B\mathbf 1\|^2=(m-2)E_1\), and the coefficient of \(E_1\) collapses to \(\Lambda_1-\Lambda_\perp\).

Under \eqref{eq:gap}, Theorem 9.1 or Theorem 10.1 gives \(\Lambda_0-\Lambda_\perp>0\) when \(m\ge 4\), and \(\Lambda_1-\Lambda_\perp>0\) in every case covered by the hypothesis. Both energies vanish only at \(B=0\), hence only at \(D=0\). The quadratic form is positive definite.

The passage from \eqref{eq:hessian-form} to the Hessian uses only that \(F_0\) is \(C^2\) and that the difference between \(F_0(D)\) and the quadratic form is \(O(\|D\|_F^3)\). For each fixed direction \(D\),
\[
\frac{F_0(tD)}{t^2}\to Q(D)\qquad(t\to 0),
\]
while the second-order Taylor expansion of the \(C^2\) function \(F_0\) gives the same limit equal to \(\tfrac12 D^2F_0(0)[D,D]\). The cubic remainder is divided by \(t^2\) and sent to \(0\). It is not differentiated.

### 11.6. Uniform convexity and enclosure

**Lemma 11.7.** Under the gap hypothesis there exist \(\delta>0\), \(\tau_*>0\), and \(\gamma>0\) such that for every \(|\tau|\le\tau_*\) and every trace-free \(D\) with \(\|D\|_F\le\delta\), the Hessian of \(F_\tau\) at \(D\) is at least \(\gamma\) times the Frobenius metric. In particular \(D=0\) is the unique minimizer of \(F_\tau\) on that ball, and
\[
F_\tau(D)\ge F_\tau(0)+\frac\gamma 2\|D\|_F^2.
\]

*Proof.* The joint map \((D,\tau)\mapsto F_\tau(D)\) is smooth near the origin because \(s(D,\tau)\) is smooth there and \(\mathcal F\) is smooth. The Hessian at \((0,0)\) is positive definite by Lemma 11.6. A positive-definite continuous matrix-valued function remains positive definite, with a uniform lower bound, on a neighborhood of the origin. The ball is convex. The first-order condition of Lemma 11.5 and the standard integration of the Hessian lower bound give the inequality.

**Lemma 11.8 (enclosure).** There is a constant \(K_m=2\alpha\sqrt m\) such that every unit-column configuration with Procrustes distance \(\rho\) satisfies, after an optimal orthogonal alignment,
\[
\|A\|_F\le K_m\rho.
\]
If the shell coordinate \(D\) of Lemma 11.4 is formed from this \(A\), then \(\|D\|_F\le K_m\rho\).

*Proof.* Alignment gives \(\|X-V\|_F=\rho\). Then
\[
G-G_\Delta=X^{\mathsf T}(X-V)+(X-V)^{\mathsf T}V,
\]
so \(\|G-G_\Delta\|_F\le 2\sqrt m\,\rho\) because each factor \(X\) or \(V\) has Frobenius norm \(\sqrt m\). The normalization \(A=\alpha(G-G_\Delta)\) contributes the factor \(\alpha\). The compressed operator \(C=(PAP)|_H\) has Frobenius norm at most \(\|A\|_F\), and the trace-free part \(D\) of \(C\) has Frobenius norm at most \(\|C\|_F\).

**Theorem 11.9 (exact small-shell minimizer).** Assume \(d\ge m\) and the gap hypothesis \eqref{eq:gap}. There exists \(\rho_0=\rho_0(m,\lambda)>0\), not evaluated numerically, such that for every \(0<\rho<\rho_0\) the following holds. Among all \(m\)-tuples of unit vectors in \(\R^d\) with \(d_P(X,\Delta)=\rho\), the decoding deficit \(\delta_\lambda\) is minimized precisely by the configurations
\begin{equation}
\label{eq:minimizer}
x_i=\kappa v_i+\sqrt{1-\kappa^2}\,z,
\qquad
\kappa=1-\frac{\rho^2}{2m},
\qquad
z\perp\operatorname{span}\{v_i\},\quad \|z\|=1,
\end{equation}
and by their images under \(O(d)\). The minimal deficit is exactly
\begin{equation}
\label{eq:delta-min}
\delta_{\min}(\rho)
=\Pc(G_\Delta;\lambda)-\Pc\Bigl(G_\Delta;\lambda\Bigl(1-\frac{\rho^2}{2m}\Bigr)\Bigr).
\end{equation}
If \(p(\lambda)=\Pc(G_\Delta;\lambda)\), then
\begin{equation}
\label{eq:even-expansion}
\delta_{\min}(\rho)
=\frac{\lambda p'(\lambda)}{2m}\rho^2
-\frac{\lambda^2 p''(\lambda)}{8m^2}\rho^4
+O(\rho^6).
\end{equation}
There is no term of order \(\rho^3\). The theorem does not apply when \(\Lambda_\perp\) equals an in-plane coefficient, and it says nothing about shells whose minimizer is forced to lie in an in-plane summand.

*Proof.* Choose \(\rho_0>0\) smaller than \(1\), smaller than \(\sqrt{2m}\), and smaller than every constraint imposed by the neighborhoods in Lemmas 11.4 and 11.7, and also smaller than \(\delta/K_m\). Then \(\kappa\in(0,1)\), every configuration on the shell \(d_P=\rho\) has, after alignment, a shell coordinate \(D\) with \(\|D\|_F\le\delta\), and \(I_H+C\succ 0\).

For any such feasible configuration the extended function \(\mathcal F\) agrees with \(\delta_\lambda\). Lemma 11.7 says that its value is at least \(F_{\rho^2}(0)\), with equality if and only if \(D=0\). It remains only to read the equality case.

If \(D=0\), the shell equation fixes \(s\) by \(\sqrt{1+s}=1-\rho^2/(2m)\). The positive number \(\kappa=1-\rho^2/(2m)\) satisfies \(\kappa^2-1=s\), so \(C=(\kappa^2-1)I_H\). The corresponding Gram matrix is
\[
G=\kappa^2 G_\Delta+(1-\kappa^2)J.
\]
Its eigenvalues on \(H\) are \(\kappa^2/\alpha>0\), and its eigenvalue on \(\operatorname{span}\{\mathbf 1\}\) is \(m(1-\kappa^2)>0\). The rank is \(m\), which is realizable in dimension \(d\ge m\) and not in a smaller dimension. One realization is \eqref{eq:minimizer}: the vector \(z\) exists because \(d-n\ge 1\), the columns are unit vectors, and Lemma 11.3 gives
\[
d_P^2=2m(1-\kappa)=\rho^2.
\]
Any two realizations of the same Gram matrix differ by an element of \(O(d)\). Permutations of the simplex vertices extend to orthogonal transformations of its span, so they do not produce a second orbit.

The common summand \(\sqrt{1-\kappa^2}\,z\) does not change the maximum-likelihood decision among the \(m\) signals. Projecting the channel onto \(\operatorname{span}\{v_i\}\) yields the simplex channel of amplitude \(\lambda\kappa\). This is \eqref{eq:delta-min}.

The simplex success probability \(p(\lambda)\) is smooth for \(\lambda>0\): differentiating \(\E\exp(\lambda\max_i\xi_i)\) under the expectation is legitimate on a neighborhood of any positive \(\lambda\) because \(\max_i\xi_i\) is sub-Gaussian. Set \(\varepsilon=\lambda\rho^2/(2m)\). Taylor expansion of \(p(\lambda-\varepsilon)\) through order \(2\) has remainder \(O(\varepsilon^3)=O(\rho^6)\) and produces \eqref{eq:even-expansion}. The exact formula depends on \(\rho\) only through \(\rho^2\), so every odd power of \(\rho\) is absent, not merely the cubic term.

The constant \(\lambda p'(\lambda)/(2m)\) equals \(\Lambda_\perp\). Indeed the path \(x_i(t)=\sqrt{1-t^2}\,v_i+tz\) has squared speed \(m\) at \(t=0\) and squared distance \(mt^2+O(t^4)\), while its deficit is \(p(\lambda)-p(\lambda\sqrt{1-t^2})=(\lambda p'(\lambda)/2)t^2+O(t^4)\). Dividing by the squared distance yields the same coefficient. This is a consistency check, not a second determination of the minimizer.

Existence of \(\rho_0\) is all that the continuity argument gives. No numerical lower bound is claimed.

## 12. Optional large-\(\mu\) asymptotics

This section is not used in Theorems 8.3, 9.1, 10.1, or 11.9.

**Proposition 12.1.** As \(\mu\to+\infty\), \(b_m(\mu)\to 1\), \(H_m(\mu)/\mu\to 1/2\), and \(a_m(\mu)/\mu^2\to 1/4\).

*Proof.* Substitute \(c=y+\mu/2\). The un-normalized density becomes a constant times \(e^{-y^2}\Phi(y+\mu/2)^{m-2}\). For \(\mu\ge 0\) the normalizing integrals are bounded above and below by positive multiples of \(\int e^{-y^2}\,dy\), because \(\Phi(y)^{m-2}\le\Phi(y+\mu/2)^{m-2}\le 1\) and the lower comparison is integrable and positive. Pointwise, \(\sigma(y+\mu/2)\to 1\), \(h(y+\mu/2)/\mu\to 1/2\), and \(h(y+\mu/2)^2/\mu^2\to 1/4\). For \(\mu\ge 1\), the bound of Lemma 1.2 supplies the integrable dominant \((|y|+1/2+\sqrt{2/\pi})^2 e^{-y^2}\). Dominated convergence gives the three limits.

The shorter bound of Lemma 8.1 already yields every limit needed for the crossing theorem. Proposition 12.1 describes the rate.

## 13. What was repaired, and what was not claimed

The coefficient list in the 30 October memorandum,
\[
h=t^{-1}-2t^{-3}+10t^{-5}+O(t^{-7}),
\qquad
\sigma=t^{-2}-6t^{-4}+50t^{-6}+O(t^{-8}),
\qquad
D=4t^{-6}+O(t^{-8}),
\]
is correct as far as it goes, but the remainder \(O(t^{-7})\) in \(h\) is one order too coarse to justify the coefficient \(50\) by algebra. The product that forms \(\sigma\) sends that unspecified \(t^{-7}\) term into the \(t^{-6}\) place. Section 3 repairs the justification by computing the coefficient \(-74\) of \(t^{-7}\) from the degree-\(4\) inversion and propagating explicit remainder bounds. The remainders are never differentiated. The first-zero argument then uses only the sign of the leading term on a far ray whose finite cutoff is not evaluated.

The lower bound \(b_4(0)\ge 1-4\sqrt 2/(3\pi+2)>1/2\) replaces the arcsin evaluation of \(J\). The arcsin formula is not proved and is not used. The inequality \(\pi>28/9\) is proved from the two-term Machin identity by computing \(\tan(4\arctan(1/5)-\arctan(1/239))=1\) and locating the angle in \((0,\pi/2)\); no decimal approximation of \(\pi\) is used.

The trace relation used below is \(S=-(m/2)\operatorname{tr} C\). The factor \(n\) appears only when \(\operatorname{tr}(sI_H)=ns\), and that substitution is what produces \(S=-(m/8)\|D\|_F^2\). The quadratic expansion \eqref{eq:quad} retains \((S^2/2)\int\omega_\lambda q^2\). On the zero-distance trace-free surface this term is \(O(\|D\|_F^4)\) and does not enter the Hessian.

The small-shell coordinate \(\kappa=1-\rho^2/(2m)\) is exact, because \(d_P^2=2m(1-\kappa)\) for the symmetric normal configuration. The quartic expansion \eqref{eq:even-expansion} matches the memorandum, including the absence of a cubic term.

No effective numerical value of \(\rho_0(m,\lambda)\) is derived. No claim is made about the minimizer on the codimension-one set where two curvatures are equal, and none is made about shells in which an in-plane summand carries the minimal curvature. Historical priority, including the agreement of the \(\mathcal H_0\) coefficient with Weber’s computation, is not part of this correctness argument.
