## Proofs in type theory

### Proofs versus proof verification

Proofs are a fundamental building block in mathematics; you detail the exact
steps to get to your conclusion (the proof), and with considerably less effort,
someone can check it is correct (proof verification).

This duality is described in great detail in computational complexity theory.
For example, for a boolean expression like $(x_1\vee x_2)\wedge(\neg x_2\vee x_3)\wedge(\neg x_3)=\text{TRUE}$ we may find a solution $(x_1,x_2,x_3)=(\text{TRUE}, \text{FALSE}, \text{FALSE})$.
To check the solution is correct, we substitute the variables for their values, and compute we get indeed $\text{TRUE}$. If instead of $n=5$ literals, we double the literals in our expression to $n=10$ literals,
it takes roughly twice as long to verify the solution. This is linear complexity, denoted $\mathcal{O}(n)$. However, the best algorithm we know to find a solution (a proof) is exponential in $n$; roughly $\mathcal{O}(1.064^n)$. [[1]] When scaling to very large $n$, finding a proof becomes prohibitively expensive in computational resources, all while verifying the solution takes only a polynomial amount of resources,
in this problem even linear.

There are many more problems that show this polynomial versus exponential seperation, and are called `NP-complete'. This divide even enabled several cryptographic technologies; a digital signature can be verified quickly (proof verification), but to forge one without the key, you are
essentially enumerating all possible proofs until one passes the verification. Notable examples
are RSA, working through integer factorisation [[2]], and Elliptic-curve cryptography, based on algebraic structures. Indeed, here we design the problem around the proof; only a specific
key will pass the proof verification.

In mathematics, perhaps the most iconic example of this disparity between
proof and proof verification complexity is Fermat's Last Theorem. It states
that for any positive integers $a$, $b$, $c$, and any integer $n>2$, the
following equation does not hold:
$$
   a^n + b^n = c^n.
$$

To disprove this statement, a proof would be just these four integer values,
and be easily checked. However, after being a conjecture for over 350 years,
it was proved no such $4$-tuple exists. 


### Encoding proofs in type theory

In the last paragraph, we saw some problems where a proof was essentially no more than a sequence of booleans or integers. Likewise, we may define





 there is no significant
faster approach than 

 For instance, integer factorisation can be formulated as such,
and forms the  [[2]]



[1]: https://arxiv.org/abs/2105.06131
[2]: https://people.csail.mit.edu/rivest/Rsapaper.pdf


in the boolean satisfiability problem, the goal is to find an interpretation
whicn makes an expression true.

 In computer science, this
duality is described in great detail in computational complexity theory;



Curry-Howard

Martin-Low

Univalence

Uniqueness of Identity Proofs (UIP)

