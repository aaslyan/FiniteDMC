# The coding theorem for finite discrete memoryless channels

**A formalization submitted for mathematical review.**

This note is for one reader: the information-theory collaborator who owns the
mathematical formulation. Its purpose is to let you evaluate the mathematics and
settle the open definitional choices **without reading Lean**. Everything below
is stated in ordinary notation; the Lean text is cited only where you might want
to check a translation.

Both theorems are proved. The proofs are complete and machine-checked, with no
unproved obligations anywhere in the development. That is precisely why §3 is not
a caveat list: the definitional choices are now load-bearing under a finished
proof, so confirming or rejecting them is a real decision with a real cost
attached.

Every claim here traces to `DOSSIER.md`, which records the evidence; Part
references are given where you might want to check one.

---

## 1. What is proved

### 1.1 Setting

Let $\mathcal X, \mathcal Y$ be finite alphabets. A **discrete memoryless
channel** is a stochastic matrix $W = \bigl(W(y \mid x)\bigr)_{x \in \mathcal X,\, y \in \mathcal Y}$.
Its $n$-fold extension is

$$W^n(y \mid x) \;=\; \prod_{i=1}^{n} W(y_i \mid x_i), \qquad x \in \mathcal X^n,\; y \in \mathcal Y^n .$$

For an input distribution $p$ on $\mathcal X$, write $\mu_p(x,y) = p(x)\,W(y\mid x)$
for the joint law and $(pW)(y) = \sum_x p(x) W(y \mid x)$ for the output marginal.
Mutual information $I(p;W)$ is the mutual information of $\mu_p$ (defined in §2.1
— **this is the choice under review**), and

$$C(W) \;=\; \sup_{p} \, I(p;W).$$

A **block code** of length $n$ is a triple $\mathcal C = (M, f, g)$ with $M \ge 1$
messages, an encoder $f : \{1,\dots,M\} \to \mathcal X^n$ and a decoder
$g : \mathcal Y^n \to \{1,\dots,M\}$. Its rate and average error probability are

$$R(\mathcal C) = \frac{\log_2 M}{n}, \qquad
P_{\mathrm e}(\mathcal C) = \frac1M \sum_{m=1}^{M} \Pr\bigl[\, g(Y^n) \ne m \;\big|\; X^n = f(m) \,\bigr].$$

Messages are uniform; the encoder and decoder are deterministic.

### 1.2 The two theorems

> **Theorem A (achievability).** Let $\mathcal X$ be nonempty, let $R < C(W)$ and
> let $\varepsilon > 0$. Then for all sufficiently large $n$ there exists a block
> code $\mathcal C$ of length $n$ with
> $$R \le R(\mathcal C) \qquad\text{and}\qquad P_{\mathrm e}(\mathcal C) \le \varepsilon .$$

> **Theorem B (weak converse).** Let $(\mathcal C_n)_{n \in \mathbb N}$ be block
> codes, $\mathcal C_n$ of length $n$, with $R \le R(\mathcal C_n)$ for every $n$
> and $P_{\mathrm e}(\mathcal C_n) \to 0$. Then $R \le C(W)$.

> **Theorem B′ (weak converse, limsup form).** If the rates
> $\bigl(R(\mathcal C_n)\bigr)_n$ are bounded above and
> $P_{\mathrm e}(\mathcal C_n) \to 0$, then
> $\limsup_n R(\mathcal C_n) \le C(W)$.

Theorem A carries the hypothesis that $\mathcal X$ is nonempty; Theorem B does
not need it. Theorem B′ is a separate statement, not a restatement of B — see
**D-10** in §3, where the boundedness hypothesis is the point.

*(Dossier Part 1.1 gives the Lean statements and their elaborated types.)*

### 1.3 Scope, stated plainly

The result is exactly this and no more:

* **Finite** input and output alphabets. Nothing about continuous or countably
  infinite channels, and nothing about Shannon–Hartley.
* **Average** error probability over uniform messages. **Not** maximal error —
  that would need an expurgation argument, and none is built.
* **Weak** converse: above capacity, the error probability cannot vanish. It is
  **not** shown that the error tends to $1$; that is the strong converse, and it
  is out of scope.
* Nothing is claimed at $R = C(W)$. Theorem A is strict below capacity, Theorem B
  strict above.
* Fixed-length block codes, deterministic encoder and decoder, no feedback.
* Zero-error capacity does not appear.

*(Dossier Parts 5.3, 5.4.)*

---

## 2. The spine of the proof

### 2.1 Entropy and mutual information

$$H(p) = -\sum_a p(a)\log_2 p(a), \qquad 0\log_2 0 := 0,$$

and for a joint law $\mu$ on $\mathcal A \times \mathcal B$ with marginals
$\mu_A, \mu_B$,

$$H(A \mid B) := H(A,B) - H(B), \qquad
\boxed{\,I(A;B) := H(A) + H(B) - H(A,B).\,}$$

The boxed definition is **D-5**, the choice most in need of your judgement (§3.1).

Two consequences are used constantly. First, the chain rule

$$H(A) = I(A;B) + H(A\mid B)$$

is an *algebraic identity* under this definition — substitute and cancel — so it
holds with no side conditions whatsoever. Second, the whole development rests on
a single analytic input, $\log t \le t - 1$, from which Gibbs' inequality,
the maximum-entropy bound $H(p) \le \log_2 |\mathcal A|$, and subadditivity all
follow. There is no appeal to Jensen's inequality or to convexity.

*(Dossier Parts 1.3, 6.3.)*

### 2.2 The converse

Let $\mathcal C$ have $M$ messages and length $n$, let $M$ be uniform, $X^n = f(M)$,
$Y^n \sim W^n(\cdot \mid X^n)$. Then

$$
\log_2 M \;\overset{(1)}{=}\; H(M)
\;\overset{(2)}{=}\; I(M;Y^n) + H(M \mid Y^n)
\;\overset{(3)}{\le}\; I(X^n;Y^n) + H(M \mid Y^n)
\;\overset{(4)}{\le}\; n\,C(W) + 1 + P_{\mathrm e}\log_2 M .
$$

(1) is the entropy of the uniform law. (2) is the chain rule, an identity as
noted. (3) is data processing along $M \to X^n \to Y^n$. (4) combines
single-letterization with Fano's inequality.

Dividing by $n$ and rearranging gives the single per-block-length inequality that
both asymptotic forms consume:

$$R(\mathcal C)\bigl(1 - P_{\mathrm e}(\mathcal C)\bigr) \;\le\; C(W) + \frac1n .$$

Letting $n \to \infty$ with $P_{\mathrm e} \to 0$ yields Theorem B.

**Step (3) is an equality, not an inequality.** The message-to-output link is the
joint law of the *composed* channel $m \mapsto W^n(\cdot \mid f(m))$, and a change
of variables along the encoder identifies $I(M;Y^n)$ with $I(X^n;Y^n)$ exactly.
The data-processing *inequality* is never needed. This surprised me and is worth
your eye. *(Dossier Part 3.4.)*

**Single-letterization.** For any joint law of the input block,

$$I(X^n;Y^n) = H(Y^n) - \sum_{i} H(Y_i \mid X_i) \le \sum_i H(Y_i) - \sum_i H(Y_i\mid X_i) = \sum_i I(X_i;Y_i) \le n\,C(W).$$

Memorylessness enters exactly once, in the first equality, and it is available
*definitionally*: the $n$-fold channel's law **is** the product $\prod_i W(y_i\mid x_i)$,
so "given $X^n$, the $Y_i$ are independent" is not a fact to establish. The only
genuine inequality is subadditivity of entropy. The final step bounds each
$I(X_i;Y_i)$ by the supremum $C(W)$, which requires knowing the supremum is over
a bounded set — see **D-7** in §3.

**Fano's inequality**, in the crude form used here:

$$H(M \mid Y^n) \;\le\; 1 + P_{\mathrm e}\,\log_2 M .$$

It is proved by Gibbs' inequality against an explicit reference weight
$w(m,y) = \nu(y)\,r(m\mid y)$, where $\nu$ is the output marginal and
$r(m \mid y) = \tfrac12$ if $m = g(y)$ and $\tfrac{1}{2(M-1)}$ otherwise. Because
Gibbs is stated for a *sub-probability* weight ($w \ge 0$, $\sum w \le 1$) rather
than a probability distribution, the degenerate case $M = 1$ needs no separate
treatment: the reference has total mass $1$ when $M \ge 2$ and $\tfrac12$ when
$M = 1$, and the inequality is indifferent.

### 2.3 Achievability

The route is **random coding with threshold decoding on the information density**,
not joint typicality. Define

$$i_p(x;y) = \log_2 \frac{W(y \mid x)}{(pW)(y)}, \qquad
i_p^{\,n}(x;y) = \sum_{j=1}^n i_p(x_j;y_j),$$

so that $\mathbb E_{\mu_p}\bigl[i_p(X;Y)\bigr] = I(p;W)$ — proved, and the bridge
between the definition in §2.1 and the quantity the argument concentrates.

The argument has three parts.

**(a) A one-shot bound.** For every threshold $\tau$ and every $M \ge 1$ there
exists a code with $M$ messages such that

$$P_{\mathrm e} \;\le\; \Pr_{\mu_p^{\,n}}\!\bigl[\, i_p^{\,n}(X^n;Y^n) \le \tau \,\bigr] \;+\; M\,2^{-\tau}.$$

The codebook is drawn i.i.d. from $p^{\,n}$ and decoded by thresholding the
likelihood ratio. A decoding error means either the true codeword failed the
threshold — the first term — or some other codeword passed it, which the union
bound and a change of measure bound by $M 2^{-\tau}$.

**(b) A weak law.** For $\delta > 0$,
$\Pr\bigl[i_p^{\,n} \le n(I(p;W) - \delta)\bigr] \to 0$. This is Chebyshev: on a
finite alphabet the information density has finite variance, and the variance of
the i.i.d. sum is $n$ times the single-letter variance. **No measure theory is
used anywhere in the development** — everything is a finite sum.

**(c) Assembly.** Given $R < I(p;W)$, take $\delta = \tfrac12\bigl(I(p;W)-R\bigr)$,
$\tau = n\bigl(I(p;W)-\delta\bigr)$ and $M = \lceil 2^{nR} \rceil$. Then (a) and
(b) drive both terms to $0$. For Theorem A, choose $p$ with $I(p;W) > R$, which
exists because $C(W)$ is a supremum; the degenerate case $R \le 0$ is handled by a
one-message code.

**This is an existence argument, and no encoder falls out of it.** The last step
of (a) is a pigeonhole: since the *average* error over the ensemble is at most the
bound, *some* codebook is at least as good as the average. That step exhibits a
good codebook and gives no procedure for finding one. It is isolated in a single
named lemma precisely so the claim is auditable rather than folklore.
*(Dossier Part 4.5.)*

**One technical remark you may want to check.** $i_p(x;y)$ must be $-\infty$ when
$W(y\mid x) = 0$ and $(pW)(y) > 0$. Under $\mu_p$ this never matters — that law
puts no mass on such pairs — but the union-bound term integrates against a
*product of marginals*, which does charge them, and there the change-of-measure
bound fails outright. The decoder therefore thresholds on the mass inequality
$2^{\tau}(pW)^n(y) < W^n(y\mid x)$, with no logarithm in it; a bridging lemma
identifies this with $i_p^{\,n} > \tau$ exactly on the support of the joint.
*(Dossier Part 4.4.)*

---

## 3. What needs your decision

**This section is the reason the note exists.** Each item below is a choice I made
to get the proof through; none has been reviewed by anyone with authority over the
mathematics. All are now load-bearing under a complete proof, so a rejection has a
cost — which is stated, so you can weigh it.

*(Dossier Part 2 records all twelve conventions with their review status.)*

### 3.1 D-5 — how mutual information is defined. **Decide this one first.**

**Current definition.**

$$I(A;B) \;=\; H(A) + H(B) - H(A,B).$$

**The alternative**, and the one most readers would expect:

$$I(A;B) \;=\; \sum_{a,b} \mu(a,b)\,\log_2 \frac{\mu(a,b)}{\mu_A(a)\,\mu_B(b)}.$$

**Why the first was chosen.** It contains no division. The relative-entropy form
has a quotient whose denominator can vanish, so every lemma stated through it
carries an implicit hypothesis that the conditioning event has positive mass —
and that is exactly the class of hypothesis that gets assumed silently rather than
discharged. With inclusion–exclusion there is nothing to assume: entropy is total,
the chain rule $H(A) = I(A;B) + H(A\mid B)$ is an algebraic identity, and no
statement anywhere in the development needs a support condition.

**What it costs.** Two things, both real:

1. **$I(A;B) \ge 0$ is not immediate.** Under the KL form it is Gibbs' inequality
   directly. Here it is subadditivity of entropy, which is a theorem. In fact it
   is **not currently proved**, because nothing in either proof needed it — see
   §4.
2. **Agreement with the KL form is a lemma, not a definition.** It is not proved.
   Anyone reading the repository and expecting the standard formula has to take
   the identification on trust, or prove it.

**The decision.** If you want the relative-entropy form as the definition, say so
now. The entropy toolkit, Fano, single-letterization and the information-density
bridge all rest on the current choice, so the change is not free — but it is far
cheaper now than after anything is built on top. If you are content with
inclusion–exclusion as the definition, the natural follow-up is to prove the KL
identification as a lemma, so that the repository connects to the standard
literature explicitly rather than by assertion.

### 3.2 The other open conventions

Each of these is genuinely open; none is merely cosmetic, but none is as
consequential as D-5.

**D-10 — the converse is stated over $R$, not $\limsup$, and this is a soundness
issue.** The natural-looking statement "$\limsup_n R(\mathcal C_n) \le C(W)$
whenever the error vanishes" is, as written, *weaker than it appears*. In Lean,
$\limsup$ of a real sequence is an infimum of eventual upper bounds; for a
sequence unbounded above that set is empty and the infimum evaluates to $0$. So an
unbounded rate sequence with vanishing error would satisfy the limsup statement
vacuously. Theorem B is therefore stated over a fixed $R$, and Theorem B′ carries
an explicit boundedness hypothesis. **Confirm that the $R$-form should be
primary.** *(Dossier Part 4.1, where this is demonstrated by a closed proof that
an unbounded sequence has $\limsup = 0$.)*

**D-7 — capacity is a supremum, and attainment is not assumed.** $C(W) = \sup_p I(p;W)$,
with attainment deliberately not a prerequisite for stating it. The same
infimum-of-empty-set phenomenon applies: an unbounded set of achievable mutual
informations would make $\sup$ evaluate to $0$. That the set is bounded is
therefore proved, not assumed, via $I \le H(Y) \le \log_2|\mathcal Y|$ — through
the *output* alphabet. *(Dossier Part 4.2.)*

**D-3 — blocks are functions $\{1,\dots,n\} \to \mathcal X$, not length-$n$
vectors.** Mathematically identical; chosen because products over coordinates are
then ordinary finite products and the type is automatically finite. No
mathematical content turns on it.

**D-8 — the message count is a natural number $M$, and the size condition is
written once, as $2^{nR} \le M$ over the reals.** No floor or ceiling appears in
any *statement* in the development; ceilings appear only inside constructions.
This was a deliberate guard against the usual source of silent off-by-one errors
in asymptotic rate bookkeeping.

**D-9 — a code does not mention the channel.** $\mathcal C = (M,f,g)$ depends only
on the alphabets; the channel enters only when the error probability is computed.
Mathematically the honest reading of what a code is, but it means one writes
$P_{\mathrm e}(\mathcal C, W)$ rather than $P_{\mathrm e}(\mathcal C)$.

---

## 4. What is not built

Stated as plainly as what is. **None of these is a gap in the two theorems** —
both are complete and unconditional. They are simply not attempted.

* **Attainment of capacity**, $\exists p,\ I(p;W) = C(W)$. Not proved. Would need
  compactness of the probability simplex and continuity of $I(\cdot\,;W)$. By
  design this is not a prerequisite for stating $C(W)$ (D-7).
* **Continuity and concavity of $I(\cdot\,;W)$.** Not proved.
* **Identification of the mutual information of §2.1 with the KL form.** Not
  proved. This is the standing cost of D-5.
* **$I(A;B) \ge 0$.** Not proved as a standalone fact — neither theorem needed it.
  Worth flagging because a reviewer would reasonably expect it to be present.
* **Joint typicality.** No typicality set exists in the development, and none is
  needed: achievability was formalized along the information-density route, which
  requires one concentration estimate rather than three. This is absent *by choice
  of route*, not by omission.
* Everything in §1.3 — maximal error, the strong converse, expurgation, feedback,
  continuous alphabets.

*(Dossier Part 5.)*

### A correction to the brief for this note

The brief asked me to record the pigeonhole step and the i.i.d. ensemble as not
yet built. **Both are built**, and I have not listed them above. The pigeonhole
"some realization beats the average" is a proved lemma; the i.i.d. ensemble is
supplied by a product-of-distributions construction written for this development,
since the Lean library has none. Earlier prose in the repository said otherwise
and was corrected before the dossier was written. *(Dossier Parts 5.1, 9.)*

---

## 5. Status, and what would help most

The development is complete: both theorems proved, no unproved obligations, and
the only axioms used are the three standard classical ones that every result in
the Lean mathematical library depends on. It builds clean.

What it does **not** have is exactly what this note asks you for. A proof
assistant can check that the derivations are valid. It cannot check that
$C(W)$, $R(\mathcal C)$, $P_{\mathrm e}(\mathcal C)$ and $I(p;W)$ mean what an
information theorist means by them. Those are stipulations, and reviewing them is
the one part of this that no machine can do.

The most useful thing you can return is a decision on **D-5**, and a yes/no on
each of D-3, D-7, D-8, D-9, D-10. If D-5 changes, it is much cheaper to change it
now than after anything else is built on top.
