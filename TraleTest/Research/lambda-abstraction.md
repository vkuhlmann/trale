# Lambda abstraction and application in Trocq

```math
\providecommand\boxbox{\boxdot} % Fall back to box dot when using KaTeX
```

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
        \Delta\vdash_t(\sigma\to\tau)\ @\ \square_i^{{\color{red}{}\delta}}\sim(\sigma'\to\tau')\because {\color{red}{}p_{\to}^{\delta}\;\sigma_R\;\tau_R}
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
arguments $a$, $a'$, we expect $f\; a$ and $f'\; a'$ to be related too. With
these rules, we can indeed derive that:
$f\;a\sim f'\;a'\because f_R\; a\; a'\; a_R$.

## When can we form the arrow type?

In Trocq, types are annotated with a map class, for example $(\text{2b}, 0)$ or
$(4, 4)$. These specify conditions satisfied when two variables satisfy the relation type. For example, $\sigma : \square^{(2b, 0)}$ guarantees that there is a map $g : \sigma\to\sigma'$, and a map $x\to\sigma_R\; x\; g(x)$. Similarly, if
we want $\sigma\to\tau : \square^{\delta}$, we need to proof properties, and
we can only do so if we have sufficient properties on $\sigma:\square^\alpha$
and $\tau:\square^\beta$.  

Let's write out some types we are dealing with:
```math
\begin{array}{l}
p_{\to}^{(0, 0)}\;\sigma_R\;\tau_R := \left(R_{\to}\;\sigma_R\;\tau_R, (\ .\ ,\ .\ )\right)\\
p_{\to}^{(1, 0)}\;\sigma_R\;\tau_R := \left(R_{\to}\;\sigma_R\;\tau_R, ((F_{\to}),\ .\ )\right)\\
p_{\to}^{(2a, 0)}\;\sigma_R\;\tau_R := \left(R_{\to}\;\sigma_R\;\tau_R, ((F_{\to}, \text{Theorem LA1}),\ .\ )\right)\\
\\\text{where}\\
R_{\to}\;\sigma_R\;\tau_R : (\sigma\to\tau)\to(\sigma'\to\tau')\to\square\\
:= \lambda f\ f'.\ \Pi (x : \sigma) (x': \sigma') (x_R : \text{rel}(\sigma_R)).\;\text{rel}(\tau_R)\;(f\ x)\;(f'\ x'),\\
\\
F_{\to} : (\sigma\to\tau)\to(\sigma'\to\tau')\\
:= \lambda f.\; f_{\tau\to\tau'} \circ f \circ f_{\sigma'\to\sigma}\\
\end{array}
```

> **Theorem LA1**  
> Assumption 1: if $f_{\tau\to\tau'}$ maps $y$ to $y'$, then $y$ and $y'$ are related.  
> Assumption 2: if $x:\sigma$ and $x':\sigma'$ are related, then $f_{\sigma'\to\sigma}\;x' = x$.  
>
> Formula to proof: $\Pi f\ f'.\ F_\to f = f'\to R_{\to}\;\sigma_R\;\tau_R\;f\,f'$  
> In words: 
> Given $f : \sigma\to\tau$ and $f' : \sigma'\to\tau'$, where $F_\to$ maps
> $f\mapsto f'$, we can produce a value of type $R_\to\;\sigma_R\;\tau_R\;f\;f'$.
> Said simple, each $f:\sigma\to\tau$ is related to $F_\to\ f:\sigma'\to\tau'$,
> and we produce the relation proof.
> 
>> _Proof._  
>> Let $f$ and $f'$ be such. Then we know $f' = f_{\tau\to\tau'}\circ f\circ f_{\sigma'\to\sigma}$.  
>> Now let $x:\sigma$, $x':\sigma'$ be arbitrary related values, say by $x_R : \sigma_R$.
>> We now need to produce a value $\tau_R\;(f\;x)\;(f'\;x')$, that is, $f\;x$ and
>> $f'\;x'$ are related.
>> By Assumption 1 it is sufficient to show $f\;x\mapsto f'\;x'$ under $f_{\tau\to\tau'}$, or
>> ```math
>> \begin{align*}
>> (f_{\tau\to\tau'}\circ f)\;x &= f'\; x'\\
>> &= (f_{\tau\to\tau'}\circ f\circ f_{\sigma'\to\sigma})\ x'\\
>> &= (f_{\tau\to\tau'}\circ f)\ (f_{\sigma'\to\sigma}\;x').
>> \end{align*}
>> ```
>> Indeed, all that is left is to show $x = f_{\sigma'\to\sigma}\;x'$. Since
>> $x$ and $x'$ are related, Assumption 2 concludes the proof.
>> 
>> _QED._


(Commutation diagram for the case (1,0).)


### What does this look like in Lean?

```lean
instance Map0_arrow
  (p1 : Param00 σ σ')
  (p2 : Param00 τ τ')
: Param00 (σ → τ) (σ' → τ') := by
  tr_constructor

  exact fun f f' =>
    forall x x', p1.R x x' -> p2.R (f a) (f' a')


instance Map1_arrow
  (p1 : Param01 σ σ')
  (p2 : Param10 τ τ')
: Param10 (σ → τ) (σ' → τ') := by
  tr_extend Map0_arrow p1 p2

  exact fun f => p2.right ∘ f ∘ p1.left

instance Map2a_arrow
  (p1 : Param02b σ σ')
  (p2 : Param2a0 τ τ')
: Param2a0 (σ → τ) (σ' → τ') := by
  tr_extend Map1_arrow p1 p2

  intro f f' mapF -- Given: f is mapped to f'
  intro x x' xR   -- Given: x and x' are related
 
  -- To proof: p2.R (f x) (f x')
  apply p2.right_implies_R
  subst mapF -- substitute f' away

  congr -- find the parts in the equality that still need to match up

  -- Remains to proof: x = p1.left x'
  exact (p1.R_implies_left x x' xR).symm

```
Now, for $\sigma:\square^\alpha$, and $\tau:\square^\beta$, we can obtain $\sigma\to\tau:\square^\delta$ if it is in the following table:

| $\delta$ | $\alpha$ | $\beta$ |
| -------- | -------- | ------- |
| (0,0)    | (0,0)    | (0,0)
| (1,0)    | (0,1)    | (1,0)
| (2a,0)   | (0,2b)   | (2a,0)
| (2b,0)   | (02a)    | (2b,0)
| (3,0)    | (0,3)    | (3,0)
| (4,0)    | (0,3)    | (4,0)

```math
% \def\mytest{\stackrel{hoi}{b}{oo}}
% \mytest

% \boxdot

% \\
% Hoi
% {\square}\mathllap{\tiny\square}

% \\
% ({\mathrlap{\,\rule 3pt 3pt}{\square}})\\

% ({\mathrlap{\,\tiny\frac{\square}{}}{\square}})
% \def\boxbox{\square\mathllap{\scalebox{0.45}{\raisebox{3.7pt}{\ensuremath{\square}\hspace{4.15pt}}}}}
% \square\above{-9pt}{\square}
% \stackrel{\square}{\square}
```


```math
% (\sigma_R : \boxbox^{\alpha}\ \sigma\ \sigma')\to(\tau_R : \boxbox^{\beta}\ \tau\ \tau')\to
% \boxbox^{\delta}\ (\sigma\to\tau)\ (\sigma'\to\tau')
% := p_{\to}^{\delta}
% \\
p_{\to}^{\delta} : \boxbox^{\alpha}\ \sigma\ \sigma'\to\boxbox^{\beta}\ \tau\ \tau'\to
\boxbox^{\delta}\ (\sigma\to\tau)\ (\sigma'\to\tau')
```

Note that with the conversion rules, the $\alpha$ or $\beta$ stated are a
minimum, and may be higher. Note we only showed $\delta$ for the second
component zero; the other cases can be derived from this: the $(0, \gamma)$
cases are
```math
p^{(0,\gamma)}_{\to}\;\sigma_R\;\tau_R := \text{swap}\left(p^{(\gamma, 0)}_{\to}\ \text{swap}(\sigma_R)\ \text{swap}({\tau_R})\right)
```
where $\text{swap} : \boxbox^{(a, b)}\ \gamma\ \gamma' \to \boxbox^{(b, a)}\ \gamma'\ \gamma$ swaps
the covariant and contravariant directions. We can also form the arrow type
$p^{(a, b)}_{\to}\;\sigma_R\;\tau_R$ where both $a$ and $b$ are nonzero; construct $p^{(a, 0)}_{\to}\;\sigma_R\;\tau_R$ and $p^{(0, b)}_{\to}\;\sigma_R\;\tau_R$ independently, and glue them together. Note that the
relation type of boths independent parts coincide, else we would not be able to glue them.

### Is the last row of the table correct?

In the last row of the table we said only $(0, 3)$ is needed on $\alpha$. This
differs from the Trocq paper, where a $(0,4)$ is specified. However, our proof
in Lean could be completed with just $(0,3)$, and I think that is indeed
sufficient.

> **Theorem LA2**  
> Given $\sigma_R: \boxbox^{(0,3)}\ \sigma\ \sigma'$ and $\tau_R: \boxbox^{(4,0)}\ \tau\ \tau'$,
> we can construct $\boxbox^{(4,0)}\ (\sigma\to\tau)\ (\sigma'\to\tau')$.
>
>> _Proof._  
>> From $p_{\to}^{(3,0)}$ we already obtain some $p:\boxbox^{(3,0)}\ (\sigma\to\tau)\ (\sigma'\to\tau')$.
>>
>> What is left to proof is $\Pi\ f\ f'\ f_R.\ \operatorname{map\_in\_R}\left(\text{R\_in\_map}(f_R)\right) = f_R$.
>> Here we use the properties $\text{map\_in\_R} : (f_{(\sigma\to\tau)\to(\sigma'\to\tau')}\ f = \ f')\to\text{rel}(p)\ f\ f' $
>> and $\text{R\_in\_map} : \text{rel}(p)\ f\ f'\to (f_{(\sigma\to\tau)\to(\sigma'\to\tau')}\ f = \ f')$.
>> These properties require $(2a,0)$ and $(2b,0)$ respectively, which are available
>> since we have $(3,0)$ on $\sigma\to\tau$.
>>
>> Essentially, we need to proof there is at most one relation object between
>> each $f:\sigma\to\tau$ and $f':\sigma'\to\tau'$. The type of relation objects is
>> $$
>>  \text{rel}(p)\ f\ f' = \Pi\ x\ x'\ x_R.\ \text{rel}(\tau_R)\ (f\ x)\ (f'\ x').
>> $$
>> There are two parts for which uniqueness is not locked down; there may be
>> multiple $x_R$ for fixed $x$, $x'$, and there may be multiple $\text{rel}(\tau_R)\ (f\ x)\ (f'\ x')$
>> for fixed $x$, $x'$ and $x_R$. Hence requiring $\sigma_R$ $\tau_R : \boxbox^{(4,0)}$ and   
>> CONTINUE  
>>We see there is an $x_R : \text{rel}(\sigma_R)$ on which a value is depedent.
>> Hence if we require $(0,4)$ for $\sigma_R$, we would lock down its uniqueness.
>> 
>> Since we have $\tau_R : \boxbox^{(4,0)}\ \tau\ \tau'$, we know that for each $y$, $y'$ there is at most one
>> $\text{rel}(\tau_R)\ y\ y'$. Now, if we assumed $\boxbox^{(0,4)}\ \sigma\ \sigma'$ like
>> the authors of the Trocq paper, we could say the same for $x_R$, and we would
>> be done. Instead, we could now have multiple $x_R$, lea
>>
>> What is left to proof 
>>
>> _QED._

We are given 
The goal is to construct





The last one says
```math
p_{\to}^{(4,0)} : \boxbox^{(0,3)}\ \sigma\ \sigma'\to\boxbox^{(4,0)}\ \tau\ \tau'\to
\boxbox^{(4,0)}\ (\sigma\to\tau)\ (\sigma'\to\tau')
```
or in Lean:
```lean
instance Map4_arrow
  (p1 : Param03 α α')
  (p2 : Param40 β β')
  : Param40 (α → β) (α' → β')
```

but according to the Trocq paper, there needs to be Param04 instead of Param03.


TODO: Check how it 



Hence to achieve the desired map class on the arrow type, we must impose  


The values of $\mathcal{D}_{\to}(\delta)$: ...

<!-- ## How do we implement it in Lean? -->



## Extending to the dependent arrow type.

For illustrative purposes we showed a version TrocqLam' and TrocqApp'
where $\tau$ is not dependent on the value of $\sigma$, i.e. $\sigma\to\tau$.
The rules can be easily modified to work for dependent arrows too. Just
replace $\sigma\to\tau$ by $\Pi x:\sigma.\ \tau$ everywhere, and replace the
single $\tau$ in TrocqApp' by $\tau[x := e_2]$. These are the proper TrocqLam
TrocqApp and are a generalisation of TrocqLam' and TrocqApp'. Furthermore,
instead of TrocqArrow we have the rule TrocqPi:
```math
\frac{
    \begin{matrix}
        \begin{matrix}
            (\alpha, \beta) = \mathcal{D}_\Pi(\delta)
            \qquad
            \Delta\vdash_t\sigma\ @\ \square_i^{\alpha}\sim \sigma'\because \sigma_R
        \end{matrix}
        \\
        \Delta, x\ @\ \sigma\sim x'\because x_R\vdash_t \tau\ @\ \square_i^{\beta}\sim\tau'\because \tau_R
    \end{matrix}
}{
    \Delta\vdash_t \Pi x: \sigma.\ \tau\ @\ \square_i^{\delta}
    \sim \Pi x' : \sigma'.\ \tau'
    \because p_{\Pi}^{\delta}\;\sigma_R\;\tau_R
}\,(\text{TrocqPi}).
```

Discussion of $\mathcal{D}_{\Pi}: ...$



---

---

# Scratch


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


