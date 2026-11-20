import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

/- English proof (translation)
Set `g : ℕ → ℕ` to `fun i => if i < d then i else if i = d + r then d else i + 1`. Establish `hg : ∀ i, i < d + r + 1 → g i < d + r + 1`. Introduce `i hi`. Simplify using `only [g]`. Apply the tactic sequence `split_ifs <;> omega`.

Set `f : Fin (d + r + 1) → Fin (d + r + 1)` to `fun i => ⟨g i, hg i i.2⟩`. Establish `hf : Function.Injective f`. Introduce `a b hab`. Establish `hab' : g a = g b` using `congrArg Fin.val hab`. Establish `ha` using `a.2`.

Establish `hb` using `b.2`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `only [g] at hab'`. Apply the tactic sequence `split_ifs at hab' <;> omega`. Use `⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp, Equiv.ofBijective_apply]`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last`. Establish `e : Fin.cast h (f (Fin.last (d + r))) = Fin.castAdd r (Fin.last d)`.

Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[f, g]`. Rewrite using `[e, Fin.append_left, Fin.snoc_last, Fin.snoc_last]`. Consider the case `cast j`. Rewrite using `[Fin.snoc_castSucc]`.

Proceed by induction on `j using Fin.addCases with`. Consider the case `left i`. Establish `e : Fin.cast h (f (Fin.castSucc (Fin.castAdd r i))) = Fin.castAdd r (Fin.castSucc i)`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[f, g]`.

Rewrite using `[e, Fin.append_left, Fin.append_left, Fin.snoc_castSucc]`. Consider the case `right i`. Establish `e : Fin.cast h (f (Fin.castSucc (Fin.natAdd d i))) = Fin.natAdd (d + 1) i`. Apply `Fin.ext` to reduce the goal to its premises. Use `i.2` as an intermediate fact.

Simplify using `[f, g]`. Apply the tactic sequence `split_ifs <;> omega`. Rewrite using `[e, Fin.append_right, Fin.append_right]`.
-/
theorem exists_perm_append_snoc {α : Type*} {d r : ℕ} (A : Fin d → α) (B : Fin r → α) (c : α)
    (h : d + r + 1 = d + 1 + r) :
    ∃ σ : Equiv.Perm (Fin (d + r + 1)),
      ((Fin.append (Fin.snoc (α := fun _ => α) A c) B) ∘ Fin.cast h) ∘ σ =
        Fin.snoc (α := fun _ => α) (Fin.append A B) c := by
  let g : ℕ → ℕ := fun i => if i < d then i else if i = d + r then d else i + 1
  have hg : ∀ i, i < d + r + 1 → g i < d + r + 1 := by
    intro i hi
    simp only [g]
    split_ifs <;> omega
  let f : Fin (d + r + 1) → Fin (d + r + 1) := fun i => ⟨g i, hg i i.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hab' : g a = g b := congrArg Fin.val hab
    have ha := a.2
    have hb := b.2
    apply Fin.ext
    simp only [g] at hab'
    split_ifs at hab' <;> omega
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), ?_⟩
  funext j
  simp only [Function.comp, Equiv.ofBijective_apply]
  induction j using Fin.lastCases with
  | last =>
    have e : Fin.cast h (f (Fin.last (d + r))) = Fin.castAdd r (Fin.last d) := by
      apply Fin.ext
      simp [f, g]
    rw [e, Fin.append_left, Fin.snoc_last, Fin.snoc_last]
  | cast j =>
    rw [Fin.snoc_castSucc]
    induction j using Fin.addCases with
    | left i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.castAdd r i))) = Fin.castAdd r (Fin.castSucc i) := by
        apply Fin.ext
        simp [f, g]
      rw [e, Fin.append_left, Fin.append_left, Fin.snoc_castSucc]
    | right i =>
      have e : Fin.cast h (f (Fin.castSucc (Fin.natAdd d i))) = Fin.natAdd (d + 1) i := by
        apply Fin.ext
        have := i.2
        simp [f, g]
        split_ifs <;> omega
      rw [e, Fin.append_right, Fin.append_right]

/- English proof (translation)
The claim follows from `show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _ from contDiffOn_const`.
-/
theorem isSmoothHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (c : ℝ) :
    IsSmoothHerm (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) :=
  show ContDiffOn ℝ _ (fun _ => Real.exp (-c)) _ from contDiffOn_const

/- English proof (translation)
Use `⟨?_, fun _ => rfl⟩` and prove the remaining obligations. Use function extensionality and compare the values at `k'`. Use `show (0 : K' → ℤ) k' = Function.extend κ (0 : K → ℤ) 0 k'`. Rewrite using `[Function.extend_def]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem isPullHerm_constLine {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (c : ℝ) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c : HermLine ι) (ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c) := by
  refine ⟨?_, fun _ => rfl⟩
  funext k'
  show (0 : K' → ℤ) k' = Function.extend κ (0 : K → ℤ) 0 k'
  classical
  rw [Function.extend_def]
  split_ifs <;> rfl

/- English proof (translation)
Introduce `hPF hEx K _ ι _ K' _ ι' _ κ v P' d r G J L L' N hb hP' hZ hJ hL hLL hN`. Take `⟨I, hI⟩` from `hEx`. Establish `hn : d + r + 1 = d + 1 + r` using `by omega`. Establish `hL' : ∀ j, IsSmoothHerm (L' j)` using `fun j => GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hb (hLL j) (hL j)`. Set `c : ℝ` to `-Real.log ((2 : ℕ) : ℝ)`.

Set `cZ : HermLine ι` to `ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c`. Set `cZ' : HermLine ι'` to `ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c`. Establish `hcZ' : IsSmoothHerm cZ'` using `isSmoothHerm_constLine c`. Establish `hcZ : IsSmoothHerm cZ` using `isSmoothHerm_constLine c`. Establish `hAN : ∀ j, IsSmoothHerm (Fin.append L' N j)`.

Introduce `j`. Proceed by induction on `j using Fin.addCases with`. Consider the case `left i => rw [Fin.append_left]`. Conclude with `hL' i`. Consider the case `right i => rw [Fin.append_right]`.

Conclude with `hN i`. Establish `hpf` using `hPF I hI K ι K' ι' κ v P' (d + 1) r G J (Fin.snoc (α := fun _ => HermLine ι) L cZ) (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N hb (hn ▸ hP') hZ hJ (fun j => by`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [Fin.snoc_last]`. Conclude with `hcZ`.

Consider the case `cast i => rw [Fin.snoc_castSucc]`. Conclude with `hL i)`. Use the proof step `(fun j => by`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => rw [Fin.snoc_last, Fin.snoc_last]`.

Conclude with `isPullHerm_constLine κ v c`. Consider the case `cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]`. Conclude with `hLL i)`. Use `hN`. Take `⟨σ, hσ⟩` from `exists_perm_append_snoc L' N cZ' hn`.

Establish `hcast : ∀ {m n : ℕ} (e : n = m) (M : Fin m → HermLine ι'), I K' ι' P' m M = I K' ι' P' n (M ∘ Fin.cast e)`. Introduce `m n e M`. Substitute `e` using the available equality. Both sides reduce to the same expression. Establish `hsmooth : ∀ j, IsSmoothHerm ((Fin.append (Fin.snoc (α` using `fun _ => HermLine ι') L' cZ') N ∘ Fin.cast hn) j) := by`.

Introduce `j`. Establish `hall : ∀ i, IsSmoothHerm (Fin.append (Fin.snoc (α` using `fun _ => HermLine ι') L' cZ') N i) := by`. Introduce `i`. Proceed by induction on `i using Fin.addCases with`. Consider the case `left i`.

Rewrite using `[Fin.append_left]`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => rw [Fin.snoc_last]`. Conclude with `hcZ'`. Consider the case `cast i => rw [Fin.snoc_castSucc]`.

Conclude with `hL' i`. Consider the case `right i => rw [Fin.append_right]`. Conclude with `hN i`. Conclude with `hall _`. Establish `hleft : I K' ι' P' (d + 1 + r) (Fin.append (Fin.snoc (α` using `fun _ => HermLine ι') L' cZ') N) = I K' ι' P' (d + r + 1) (Fin.snoc (α := fun _ => HermLine ι') (Fin.append L' N) cZ') := by`.

Rewrite using `[hcast hn, ← hσ]`. Conclude with `((hI K' ι').1 P' (d + r + 1) _ σ hP' hsmooth).symm`. Establish `h2 : Nat.Prime 2` using `Nat.prime_two`. Establish `hconsL` using `(GroundTheory.Heights₂.Heights.Inter.Conservation.proof K' ι' (I K' ι') (hI K' ι') P' (d + r) (Fin.append L' N) 2 hP' hAN h2).2`. Establish `hconsR` using `(GroundTheory.Heights₂.Heights.Inter.Conservation.proof K ι (I K ι) (hI K ι) (imageZ v P') d L 2 hZ hL h2).2`.

Establish `hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0`. Establish `: (1 : ℝ) < ((2 : ℕ) : ℝ)` using `by norm_num`. Conclude with `(Real.log_pos this).ne'`. Rewrite `hpf` using `[hleft]`. Establish `e1 : Real.log ((2 : ℕ) : ℝ) * ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) = Real.log ((2 : ℕ) : ℝ) * ((J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (imageZ v P') (pot L) (fun _ => 1))`.

Rewrite using `[← hconsL]`. Use `hpf.trans ?_` and prove the remaining obligations. Rewrite using `[hconsR]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `mul_left_cancel₀ hlog e1`.
-/
theorem ptsIntegral_projection : PFStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.ExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d r : ℕ) (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ)) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'), IsBlockMap κ v → IsArithVar P' (d + r + 1) → IsArithVar (imageZ v P') (d + 1) → IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) → ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) = (J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) * ptsIntegral (imageZ v P') (pot L) (fun _ => 1) := by
  intro hPF hEx K _ ι _ K' _ ι' _ κ v P' d r G J L L' N hb hP' hZ hJ hL hLL hN
  obtain ⟨I, hI⟩ := hEx
  have hn : d + r + 1 = d + 1 + r := by omega
  have hL' : ∀ j, IsSmoothHerm (L' j) := fun j =>
    GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hb (hLL j) (hL j)
  let c : ℝ := -Real.log ((2 : ℕ) : ℝ)
  let cZ : HermLine ι := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  let cZ' : HermLine ι' := ReciprocityTheory.ChartRestriction.G.AI.I2.constLine c
  have hcZ' : IsSmoothHerm cZ' := isSmoothHerm_constLine c
  have hcZ : IsSmoothHerm cZ := isSmoothHerm_constLine c
  have hAN : ∀ j, IsSmoothHerm (Fin.append L' N j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact hL' i
    | right i => rw [Fin.append_right]; exact hN i

  have hpf := hPF I hI K ι K' ι' κ v P' (d + 1) r G J (Fin.snoc (α := fun _ => HermLine ι) L cZ)
    (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N hb (hn ▸ hP') hZ hJ
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last]; exact hcZ
      | cast i => rw [Fin.snoc_castSucc]; exact hL i)
    (fun j => by
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_last]; exact isPullHerm_constLine κ v c
      | cast i => rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hLL i)
    hN

  obtain ⟨σ, hσ⟩ := exists_perm_append_snoc L' N cZ' hn
  have hcast : ∀ {m n : ℕ} (e : n = m) (M : Fin m → HermLine ι'),
      I K' ι' P' m M = I K' ι' P' n (M ∘ Fin.cast e) := by
    intro m n e M
    subst e
    rfl
  have hsmooth : ∀ j, IsSmoothHerm
      ((Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N ∘ Fin.cast hn) j) := by
    intro j
    have hall : ∀ i, IsSmoothHerm (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N i) := by
      intro i
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        induction i using Fin.lastCases with
        | last => rw [Fin.snoc_last]; exact hcZ'
        | cast i => rw [Fin.snoc_castSucc]; exact hL' i
      | right i => rw [Fin.append_right]; exact hN i
    exact hall _
  have hleft : I K' ι' P' (d + 1 + r) (Fin.append (Fin.snoc (α := fun _ => HermLine ι') L' cZ') N) =
      I K' ι' P' (d + r + 1) (Fin.snoc (α := fun _ => HermLine ι') (Fin.append L' N) cZ') := by
    rw [hcast hn, ← hσ]
    exact ((hI K' ι').1 P' (d + r + 1) _ σ hP' hsmooth).symm

  have h2 : Nat.Prime 2 := Nat.prime_two
  have hconsL := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K' ι' (I K' ι') (hI K' ι') P' (d + r)
    (Fin.append L' N) 2 hP' hAN h2).2
  have hconsR := (GroundTheory.Heights₂.Heights.Inter.Conservation.proof K ι (I K ι) (hI K ι) (imageZ v P') d L 2 hZ hL h2).2
  have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
    exact (Real.log_pos this).ne'
  rw [hleft] at hpf
  have e1 : Real.log ((2 : ℕ) : ℝ) * ptsIntegral P' (pot (Fin.append L' N)) (fun _ => 1) =
      Real.log ((2 : ℕ) : ℝ) * ((J (fibreIdeal κ G) r (fun j => fibreDeg κ (N j).a) : ℝ) *
        ptsIntegral (imageZ v P') (pot L) (fun _ => 1)) := by
    rw [← hconsL]
    refine hpf.trans ?_
    rw [hconsR]
    ring
  exact mul_left_cancel₀ hlog e1

end GlobalTheory.CompanionTheory.Ar.Giv
