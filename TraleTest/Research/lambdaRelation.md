# Lambda abstraction and application in Trocq

The Trocq framework is built on top of the Calculus of Constructions
($CC_{\omega}^{+}$), since this also underpins Rocq. We use Lean, which uses a similar calculus, but still has a common important building block: the simply typed lambda calculus ($\lambda^{\to}$). This main features of this calculus are these rules: [[1]]
```math
   \frac{
    \begin{matrix}
        \Gamma \vdash \sigma : \square_i
        \\
        \Gamma, x:\sigma \vdash e:\tau
    \end{matrix}
   }{
    \Gamma\vdash (\lambda x:\sigma.\ e):(\sigma \to \tau)
   }
   \,(\text{Lam})\qquad
   \frac{
    \Gamma\vdash e_1:\sigma\to\tau\quad\Gamma\vdash e_2:\sigma
   }{
    \Gamma\vdash e_1\;e_2:\tau
   }
   \,(\text{App})
   \qquad
   \frac{
    \Gamma\vdash\sigma:\square_i\quad \Gamma\vdash\tau:\square_i
   }{
    \Gamma\vdash (\sigma\to\tau) : \square_i
   }
   \,(\text{Arrow})
```

[1]: https://en.wikipedia.org/wiki/Simply_typed_lambda_calculus

The first says how to form an arrow type (lambda abstraction), the second how to use it (application),
and lastly, we can form the arrow type between arbitrary types. The last rule is
largely implied by the first, but clarifies that even if we can't demonstrate a
value of each type, we can form the arrow type. This is especially useful when the type might be
a proposition to proof, for which demonstrating a value is their entire \textsl{raison d'être}, and
so the only scope we already need to use them in. It also states the universe level is the
same as its two composing types.

 <!-- Mostly is the keyword,
since 

 The last rule
is already implied in many cases by Lam; if we know a possible value for each
type, then it validates the arrow type itself -->

Note: The notation $e_1\;e_2$ means we're applying $e_2$ as an argument to $e_1$. Where you would write $f(x)$ in other fields of mathematics, we write $f\;x$.

<!-- The lambda abstraction
They define an arrow type $\sigma\to\tau$ by the underlying lambda taking values of type $\sigma$ to values of type $\tau$ (Lam), and that its application with any argument of type $\sigma$ yields a value of type $\tau$ (App). -->

In the Trocq framework, we need to encode more information; an occurrence of $\sigma:\square_i$
becomes $\sigma\ @\ \square_i^{\alpha} \sim \sigma'\because \sigma_R$, and an
occurrence of $x : \sigma$ becomes $x\ @\ \sigma\sim x'\because x_R$. With
this, the rules become:
```math
    \frac{
        \begin{matrix}
            \Delta\vdash_t\ \sigma @\ \square_i^{\alpha}\sim \sigma'\because \sigma_R\\
            \Delta, x\ @\ \sigma \sim x'\because x_R
            \vdash_t e\ @\ \tau\sim e'\because e_R
        \end{matrix}
        }{
            \Delta\vdash_t (\lambda x:\sigma.\ e)\ @\ (\sigma \to \tau)\sim (
            \lambda x' : \sigma'.\,e'){\color{red}{}\because\lambda x\,x'\,x_R.\ e_R}
        }
        \,(\text{TrocqLam'})
```
```math
    \frac{
        \begin{matrix}
            \Delta\vdash_t\ e_1\ @\ (\sigma\to\tau)\sim\sigma'\because (e_1)_R
            \quad
            \Delta\vdash_t\ e_2\ @\ \sigma\sim e_2'\because (e_2)_R
        \end{matrix}
    }{
        \Delta\vdash_t e_1\;e_2\ @\ \tau \sim e_1'\;e_2'{\color{red}{}\because (e_1)_R\; e_2\; e_2'\; (e_2)_R}
    }
    \,(\text{TrocqApp'})
```
```math
    \frac{
        \begin{matrix}
            {\color{red}{}(\alpha, \beta) = \mathcal{D}_{\to}(\delta)}\\
            \Delta\vdash_t\sigma\ @\ \square_i^{\alpha}\sim\sigma'\because\sigma_R
            \qquad
            \Delta\vdash_t\tau\ @\ \square_i^{\beta}\sim\tau'\because\tau_R
        \end{matrix}
    }{
        \Delta\vdash_t(\sigma\to\tau)\ @\ \square_i^{{\color{red}{}\delta}}\sim(\sigma'\to\tau')\because {\color{red}{}p_{\to}^{\delta}\;A_R\;B_R}
    }
    \,(\text{TrocqArrow})
```

Note that we introduced various variables to capture the extra information,
and we are using $\Delta$ and $\vdash_t$ instead of $\Gamma$ and $\vdash$
to make clear we are now talking about the environment and judgment from the
Trocq calculus instead of the simply typed lambda calculus. 

Suddenly, the Arrow rule has become the most interesting one; we are introducing a map class variable,
but it shouldn't be unconstrained, we only want it to take values compatible with
the rest of the Trocq framwork. We are doing that with the extra condition. For
some combinations of $\alpha$ and $\beta$, there is not even any
$\delta$ allowed, so we can't form the arrow type! We will dive into the
discussion of $\mathcal{D}$ shortly.

Another thing to notice is that we are using lambda abstraction and applications
also in the relation proofs of TrocqLam' and TrocqApp'. They encode a very
natural use; if we have two related functions $f$, $f'$ and two related
arguments $a$, $a'$, we expect $f\; a$ and $f'\; a'$ to
be related too. With these rules, we can indeed derive that:
$f\;a\sim f'\;a'\because f_R\; a\; a'\; a_R$.

## When can we form the arrow type?

The values of $\mathcal{D}_{\to}(\delta)$: ...

## How do we implement it in Lean?



## Extending to the dependent arrow type.


Remark: for illustrative purposes we showed a version TrocqLam' and TrocqApp'
where $\tau$ is not dependent on the value of $\sigma$, i.e. $\sigma\to\tau$.
The rules can be easily modified to work for dependent arrows too. Just
replace $\sigma\to\tau$ by $\Pi x:\sigma. \tau$ everywhere, and replace the
single $\tau$ in TrocqApp' by $\tau[x := e_2]$.



Remark; the $\sigma\to\tau$ in TrocqLam' and TrocqApp' can be replaced by $\Pi x:\sigma. \tau$ to denote
$\tau$ can depend on the value of $\sigma$. Doing so yields the TrocqLam 
and TrocqApp rule as defined
in the Trocq framwork. For illustrative purposes, we showed here the special case $\sigma\to\tau$ where
$\tau$ does not depend on the value of $\sigma$.


 How
should we fill in this extra information for the Trocq equivalents of these
rules? We will 




The
Trocq rules of lambda abstraction will hence need to fill 

 the types, like $\sigma$ and $\tau$ don't come alone; but in quadruples like $\sigma\ @\ \square_i^{\alpha} \sim \sigma' \because \sigma_R$, or $x\ @\ \sigma \sim x'\because x_R$ for its values. This poses the question: what is a sufficient consistency rule for arrow types, in terms of these quadruples?

Let's rewrite the rules with these quadruples, using placeholders for the extra information our quadruples encode:


<!-- We have several considerations: -->

Let's make some observations:

- aa


In the case of the Trocq framwork, we 

 applying an argument to it the resulting type of a function application $(e_1 : \sigma\to\tau)\, (e_2 : \sigma)$


 <!-- $
\begin{prooftree}
\AxiomC{A}
\UnaryInfC{B}
\AxiomC{C}
\BinaryInfC{D}
\AxiomC{E}
\AxiomC{F}
\BinaryInfC{G}
\UnaryInfC{H}
\BinaryInfC{J}
\end{prooftree}$ -->



The Calculus of Constructions ($CC_{\omega}^{+}$) which the Trocq frameworks
is built on top of (as it is )

A core part of the Calculus of Constructions ($CC_{\omega}^{+}$) is function application and lambda abstraction.
If we know that $a$ and $b$ are 
 
The Trocq framework defines the following typing rules for lambda abstraction,
and lambda application:

<!-- ![Application typing rule](./typing_rules/param-app.png)

![Lambda abstraction typing rule](./typing_rules/param-lam.png) -->

In Lean code, this amounts to the following:


