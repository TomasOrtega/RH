import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ComapFgOfValuationRing
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbProj
import Development.WeilBound.CoreStatements.HodgeTatePoints.RbTriang

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rb

section general

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]
  {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N]

variable (C) in

noncomputable def Phi (p f : ℕ) {n : ℕ} (b : Module.Basis (Fin n) F N) (σ : MulChar F R) :
    (Fin n × Fin f → R) →ₗ[R] (N → C) :=
  Fintype.linearCombination R
    fun (j : Fin n × Fin f) (x : N) => algebraMap R C ((σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1))

variable {p f n : ℕ} {b : Module.Basis (Fin n) F N} {σ : MulChar F R}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_afLatT {M : Submodule R (N → C)} {l : Fin n × Fin f → R} :
    l ∈ afLatT p f b σ M ↔ Phi C p f b σ l ∈ M ⊔ pFun R p N := Iff.rfl

/- English proof (translation)
Simplify using `[Phi, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def]`.
-/
theorem Phi_apply (l : Fin n × Fin f → R) (x : N) :
    Phi C p f b σ l x =
      algebraMap R C (∑ j : Fin n × Fin f, l j * (σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1)) := by
  simp [Phi, Fintype.linearCombination_apply, Finset.sum_apply, Algebra.smul_def]

/- English proof (translation)
Rewrite using `[Phi_apply, Finset.sum_eq_single (i, s)]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨j, t⟩ _ hne`. Distinguish the cases in `ht : t = s`. Substitute `ht` using the available equality.

Establish `: j ≠ i` using `fun h => hne (by rw [h])`. Simplify using `[Finsupp.single_apply, this.symm, MulChar.map_zero]`. Rewrite using `[hl (j, t) ht, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem Phi_basis (l : Fin n × Fin f → R) (s : Fin f) (hl : ∀ j, j.2 ≠ s → l j = 0) (i : Fin n) :
    Phi C p f b σ l (b i) = algebraMap R C (l (i, s)) := by
  classical
  rw [Phi_apply, Finset.sum_eq_single (i, s)]
  · simp
  · rintro ⟨j, t⟩ _ hne
    by_cases ht : t = s
    · subst ht
      have : j ≠ i := fun h => hne (by rw [h])
      simp [Finsupp.single_apply, this.symm, MulChar.map_zero]
    · rw [hl (j, t) ht, zero_mul]
  · simp

/- English proof (translation)
Rewrite using `[Phi_apply, Phi_apply, ← map_mul, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : j.2 = s`. Rewrite using `[h, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hl j h]`. Simplify using the standard rewrite rules.
-/
theorem Phi_eigen (l : Fin n × Fin f → R) (s : Fin f) (hl : ∀ j, j.2 ≠ s → l j = 0) (a : F)
    (x : N) : Phi C p f b σ l (a • x) =
      algebraMap R C ((σ ^ p ^ (s : ℕ)) a) * Phi C p f b σ l x := by
  rw [Phi_apply, Phi_apply, ← map_mul, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.2 = s
  · rw [h, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
    ring
  · rw [hl j h]
    simp

/- English proof (translation)
Rewrite using `[Phi_apply, Finset.sum_eq_zero, map_zero]`. Introduce `j _`. Distinguish the cases in `h : j.1 < i`. Rewrite using `[hl j h, zero_mul]`. Establish `: b.repr x j.1 = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `h (b.repr_support_subset_of_mem_span _ hx (Finsupp.mem_support_iff.2 h0))`. Rewrite using `[this, MulChar.map_zero, mul_zero]`.
-/
theorem Phi_flag (l : Fin n × Fin f → R) (i : Fin n) (hl : ∀ j, j.1 < i → l j = 0) (x : N)
    (hx : x ∈ flagSub b i) : Phi C p f b σ l x = 0 := by
  rw [Phi_apply, Finset.sum_eq_zero, map_zero]
  intro j _
  by_cases h : j.1 < i
  · rw [hl j h, zero_mul]
  · have : b.repr x j.1 = 0 := by
      by_contra h0
      exact h (b.repr_support_subset_of_mem_span _ hx (Finsupp.mem_support_iff.2 h0))
    rw [this, MulChar.map_zero, mul_zero]

/- English proof (translation)
Rewrite using `[mem_pFun]`. Introduce `x`. Rewrite using `[Phi_apply, mem_pInt_iff hinj]`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hl j)`.
-/
theorem Phi_mem_pFun (hinj : Function.Injective (algebraMap R C)) (l : Fin n × Fin f → R)
    (hl : ∀ j, l j ∈ Ideal.span {(p : R)}) : Phi C p f b σ l ∈ pFun R p N := by
  rw [mem_pFun]
  intro x
  rw [Phi_apply, mem_pInt_iff hinj]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hl j)

/- English proof (translation)
The claim follows from `mem_afLatT.2 (Submodule.mem_sup_right (Phi_mem_pFun hinj l hl))`.
-/
theorem mem_afLatT_of_p (hinj : Function.Injective (algebraMap R C)) (M : Submodule R (N → C))
    (l : Fin n × Fin f → R) (hl : ∀ j, l j ∈ Ideal.span {(p : R)}) : l ∈ afLatT p f b σ M :=
  mem_afLatT.2 (Submodule.mem_sup_right (Phi_mem_pFun hinj l hl))

/- English proof (translation)
Use `⟨fun x => ⟨_, (Phi_apply l x).symm⟩, fun x y => ?_⟩` and prove the remaining obligations. Rewrite using `[Phi_apply, Phi_apply, Phi_apply, ← map_sub, ← map_sub, mem_pInt_iff hinj, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Ideal.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_sub, ← mul_sub, map_add, Finsupp.add_apply]`. Conclude with `Ideal.mul_mem_left _ _ (FundGen.frob_pow_additive p F σ hσ _ _ _)`.
-/
theorem Phi_mem_linFun [Fact p.Prime] [CharP F p] (hinj : Function.Injective (algebraMap R C))
    (hσ : IsFund p σ) (l : Fin n × Fin f → R) : Phi C p f b σ l ∈ linFun R p N := by
  refine ⟨fun x => ⟨_, (Phi_apply l x).symm⟩, fun x y => ?_⟩
  rw [Phi_apply, Phi_apply, Phi_apply, ← map_sub, ← map_sub, mem_pInt_iff hinj,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Ideal.sum_mem _ fun j _ => ?_
  rw [← mul_sub, ← mul_sub, map_add, Finsupp.add_apply]
  exact Ideal.mul_mem_left _ _ (FundGen.frob_pow_additive p F σ hσ _ _ _)

/- English proof (translation)
Introduce `g hg x y` and use `Submodule.sub_mem _ (Submodule.sub_mem _ (mem_pFun.1 hg _) (mem_pFun.1 hg _)) (mem_pFun.1 hg _)`.
-/
theorem pFun_le_addFun : pFun (C := C) R p N ≤ addFun R p N := fun g hg x y =>
  Submodule.sub_mem _ (Submodule.sub_mem _ (mem_pFun.1 hg _) (mem_pFun.1 hg _)) (mem_pFun.1 hg _)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Use `Submodule.neg_mem _ (hg 0 0)` as an intermediate fact. Simplify using `using this`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Use `Submodule.add_mem _ (hg (y a) (∑ i ∈ s, y i)) ih using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem addFun_sum {g : N → C} (hg : g ∈ addFun R p N) {ι : Type} (s : Finset ι) (y : ι → N) :
    g (∑ i ∈ s, y i) - ∑ i ∈ s, g (y i) ∈ pInt (C := C) R p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Submodule.neg_mem _ (hg 0 0)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    convert Submodule.add_mem _ (hg (y a) (∑ i ∈ s, y i)) ih using 1
    ring

/- English proof (translation)
Take `⟨g1, h1, g2, h2, rfl⟩` from `Submodule.mem_sup.1 hg`. Conclude with `Submodule.add_mem_sup (hst a g1 h1) (mem_pFun.2 fun x => mem_pFun.1 h2 _)`.
-/
theorem sup_stable {M : Submodule R (N → C)} (hst : FStable F M) {g : N → C}
    (hg : g ∈ M ⊔ pFun R p N) (a : F) : (fun x => g (a • x)) ∈ M ⊔ pFun R p N := by
  obtain ⟨g1, h1, g2, h2, rfl⟩ := Submodule.mem_sup.1 hg
  exact Submodule.add_mem_sup (hst a g1 h1) (mem_pFun.2 fun x => mem_pFun.1 h2 _)

def cut (s : Fin f) (l : Fin n × Fin f → R) : Fin n × Fin f → R :=
  fun j => if j.2 = s then l j else 0

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[cut, Finset.sum_apply]`.
-/
theorem sum_cut (l : Fin n × Fin f → R) : ∑ s, cut s l = l := by
  funext j
  simp [cut, Finset.sum_apply]

/- English proof (translation)
Introduce `_ h` and use `if_neg h`.
-/
theorem cut_supp (s : Fin f) (l : Fin n × Fin f → R) : ∀ j, j.2 ≠ s → cut s l j = 0 :=
  fun _ h => if_neg h

/- English proof (translation)
Use `conv_lhs => rw [← sum_cut l, map_sum, ← projL_apply, map_sum]`. Rewrite using `[Finset.sum_eq_single s]`. Conclude with `proj_eigen_self h0 _ _ (Phi_eigen _ s (cut_supp s l))`. Introduce `t _ ht`. Conclude with `proj_eigen_ne (fun h => ht (hinj _ _ h).symm) _ (Phi_eigen _ t (cut_supp t l))`.

Simplify using the standard rewrite rules.
-/
theorem proj_Phi [Fintype F] [DecidableEq F] [IsDomain R] (h0 : (Fintype.card Fˣ : C) ≠ 0)
    (hinj : ∀ s t : Fin f, σ ^ p ^ (s : ℕ) = σ ^ p ^ (t : ℕ) → s = t)
    (l : Fin n × Fin f → R) (s : Fin f) :
    proj (σ ^ p ^ (s : ℕ)) (Phi C p f b σ l) = Phi C p f b σ (cut s l) := by
  conv_lhs => rw [← sum_cut l, map_sum, ← projL_apply, map_sum]
  rw [Finset.sum_eq_single s]
  · exact proj_eigen_self h0 _ _ (Phi_eigen _ s (cut_supp s l))
  · intro t _ ht
    exact proj_eigen_ne (fun h => ht (hinj _ _ h).symm) _ (Phi_eigen _ t (cut_supp t l))
  · simp

end general

/- English proof (translation)
Use `choose r hr using hg.1`. Use `choose β hβ _ using fun i : Fin n => moore p C v R hv hp F f hc σ hσ (fun a => r (a • b i)) fun a a' => by`. Rewrite using `[← mem_pInt_iff hv.hom_inj, map_sub, map_sub, hr, hr, hr, add_smul]`. Conclude with `hg.2 _ _`. Use `⟨fun j => β j.1 j.2, mem_pFun.2 fun x => ?_⟩` and prove the remaining obligations.

Establish `h1` using `addFun_sum hg.2 Finset.univ fun i => b.repr x i • b i`. Rewrite `h1` using `[b.sum_repr]`. Establish `h2` using `(mem_pInt_iff hv.hom_inj p _).2 (Ideal.sum_mem _ (t := Finset.univ) fun i _ => hβ i (b.repr x i))`. Use `Submodule.add_mem _ h1 h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[Pi.sub_apply, Phi_apply, Fintype.sum_prod_type, Finset.sum_sub_distrib, map_sub]`.

Simplify using `only [map_sum, hr]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_Phi (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] (hv : v.Integers R)
    (hp : v (p : C) < 1) {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F p] {f : ℕ}
    (hc : Fintype.card F = p ^ f) {N : Type} [AddCommGroup N] [Module F N] {σ : MulChar F R}
    (hσ : IsFund p σ) {n : ℕ} (b : Module.Basis (Fin n) F N) {g : N → C}
    (hg : g ∈ linFun R p N) : ∃ l, g - Phi C p f b σ l ∈ pFun R p N := by
  choose r hr using hg.1
  choose β hβ _ using fun i : Fin n =>
    moore p C v R hv hp F f hc σ hσ (fun a => r (a • b i)) fun a a' => by
      rw [← mem_pInt_iff hv.hom_inj, map_sub, map_sub, hr, hr, hr, add_smul]
      exact hg.2 _ _
  refine ⟨fun j => β j.1 j.2, mem_pFun.2 fun x => ?_⟩
  have h1 := addFun_sum hg.2 Finset.univ fun i => b.repr x i • b i
  rw [b.sum_repr] at h1
  have h2 := (mem_pInt_iff hv.hom_inj p _).2
    (Ideal.sum_mem _ (t := Finset.univ) fun i _ => hβ i (b.repr x i))
  convert Submodule.add_mem _ h1 h2 using 1
  rw [Pi.sub_apply, Phi_apply, Fintype.sum_prod_type, Finset.sum_sub_distrib, map_sub]
  simp only [map_sum, hr]
  ring

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hst σ hσ n b`. Use `haveI : IsDomain R := hv.hom_inj.isDomain`. Use `haveI : ValuationRing R := ValuationRing.of_integers v hv`. Take `⟨h0, w, hw⟩` from `exists_inv_card hv hp hc`. Establish `hinj` using `hv.hom_inj`.

Establish `hdist` using `fund_pow_inj p v R hv hp F f hc σ hσ`. Establish `hgrade : ∀ l ∈ afLatT p f b σ AA.carrier, ∀ s : Fin f, cut s l ∈ afLatT p f b σ AA.carrier`. Introduce `l hl s`. Rewrite using `[mem_afLatT, ← proj_Phi h0 hdist]`. Conclude with `proj_mem hw _ _ _ (sup_stable hst (mem_afLatT.1 hl))`.

Establish `haf : ∀ l ∈ afLatT p f b σ AA.carrier, ∃ g ∈ afFun p AA.carrier, g - Phi C p f b σ l ∈ pFun R p N`. Introduce `l hl`. Take `⟨g, hg, h, hh, e⟩` from `Submodule.mem_sup.1 (mem_afLatT.1 hl)`. Use `⟨g, ⟨hg, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_sub_of_add_eq e]`.

Conclude with `Submodule.sub_mem _ (Phi_mem_linFun hinj hσ l).2 (pFun_le_addFun hh)`. Rewrite using `[← e]`. Simplify using `using Submodule.neg_mem _ hh`. Use `⟨?_, ?_, hgrade, fun i s c => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Set `ι : (N → R) →ₗ[R] (N → C)` to `(Algebra.linearMap R C).compLeft N`.

Establish `hι : Function.Injective ι` using `fun x y h => funext fun k => hinj (congrFun h k)`. Set `Φ : (Fin n × Fin f → R) →ₗ[R] (N → R)` to `Fintype.linearCombination R fun (j : Fin n × Fin f) (x : N) => (σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1)`. Establish `hΦ : Phi C p f b σ = ι ∘ₗ Φ`. Use `LinearMap.ext fun l => funext fun x => ?_` and prove the remaining obligations. Rewrite using `[Phi_apply]`.

Simplify using `[ι, Φ, Fintype.linearCombination_apply, Finset.sum_apply]`. Establish `hfg : (AA.carrier ⊔ pFun R p N).FG`. Use `Submodule.FG.sup ?_ (Submodule.fg_pi fun _ => Submodule.fg_span_singleton _)` and prove the remaining obligations. Take `⟨B, -, hB⟩` from `AA.lat`. Rewrite using `[hB]`.

Conclude with `Submodule.fg_span (Set.finite_range _)`. Establish `hle : AA.carrier ⊔ pFun R p N ≤ LinearMap.range ι`. Establish `hint : intFun R N ≤ LinearMap.range ι`. Introduce `g hg`. Use `choose r hr using hg`.

Conclude with `⟨r, funext hr⟩`. Use `le_trans (sup_le AA.le_int fun g hg x => ?_) hint` and prove the remaining obligations. Take `⟨c, hc⟩` from `Submodule.mem_span_singleton.1 (mem_pFun.1 hg x)`. Conclude with `⟨c * p, by rw [← hc, Algebra.smul_def, map_mul, map_natCast]⟩`. Establish `h1 : ((AA.carrier ⊔ pFun R p N).comap ι).FG` using `Submodule.fg_of_fg_map_injective ι hι (by rw [Submodule.map_comap_eq_self hle]; exact hfg)`.

Establish `h2` using `comap_fg_of_valuationRing R _ _ Φ _ h1`. Rewrite `h2` using `[← Submodule.comap_comp, ← hΦ]`. Conclude with `h2`. Set `Φ : (Fin n × Fin f → R) →ₗ[R] linFun (C` to `C) R p N := (Phi C p f b σ).codRestrict _ (Phi_mem_linFun hinj hσ)`. Set `θ : (Fin n × Fin f → R) →ₗ[R] AFQuot p AA.carrier` to `Submodule.mkQ _ ∘ₗ Φ`.

Establish `hsurj : Function.Surjective θ`. Introduce `q`. Take `⟨g, rfl⟩` from `Submodule.Quotient.mk_surjective _ q`. Take `⟨l, hl⟩` from `exists_Phi p hv hp hc hσ b g.2`. Use `⟨l, ((Submodule.Quotient.eq _).2 ?_).symm⟩` and prove the remaining obligations.

Conclude with `Submodule.mem_sup_right hl`. Establish `hker : LinearMap.ker θ = afLatT p f b σ AA.carrier`. Use extensionality with `l`. Establish `: l ∈ LinearMap.ker θ ↔ Phi C p f b σ l ∈ afFun p AA.carrier ⊔ pFun R p N` using `Submodule.Quotient.mk_eq_zero _`. Rewrite using `[this]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hle : afFun p AA.carrier ⊔ pFun R p N ≤ AA.carrier ⊔ pFun R p N` using `sup_le_sup_right (fun _ hx => hx.1) _`. Conclude with `mem_afLatT.2 (hle h)`. Introduce `h`.

Take `⟨g, hg, hh⟩` from `haf l h`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left (T := pFun R p N) hg) (Submodule.mem_sup_right hh)` as an intermediate fact. Simplify using `using this`. Conclude with `⟨(θ.quotKerEquivOfSurjective hsurj).symm.trans (Submodule.quotEquivOfEq _ _ hker)⟩`. Introduce and unpack `⟨g, hg, h1, h2, h3⟩`.

Take `⟨l, hl⟩` from `exists_Phi p hv hp hc hσ b (g := g) ⟨AA.le_int hg.1, hg.2⟩`. Establish `hlL : l ∈ afLatT p f b σ AA.carrier`. Use `Submodule.sub_mem _ (Submodule.mem_sup_left (T := pFun R p N) hg.1) (Submodule.mem_sup_right hl)` as an intermediate fact. Rewrite using `[mem_afLatT]`. Simplify using `using this`.

Establish `e1 : proj (σ ^ p ^ (s : ℕ)) g - Phi C p f b σ (cut s l) ∈ pFun R p N`. Rewrite using `[← proj_Phi h0 hdist, ← projL_apply, ← projL_apply, ← map_sub]`. Conclude with `proj_mem hw _ _ _ fun a => mem_pFun.2 fun x => mem_pFun.1 hl _`. Establish `e2 : proj (σ ^ p ^ (s : ℕ)) g - g ∈ pFun R p N`. Rewrite using `[mem_pFun]`.

Introduce `x`. Use `Submodule.smul_mem _ w (Submodule.sum_mem _ (t := Finset.univ) fun (a : Fˣ) _ => Submodule.smul_mem _ ((σ ^ p ^ (s : ℕ))⁻¹ (a : F)) (h1 a x))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Simplify using `only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← map_mul, inv_mul_apply, hw, Pi.sub_apply, proj]`. Simplify using `[h0]`.

Establish `e3 : ∀ j, g (b j) - algebraMap R C (l (j, s)) ∈ pInt (C` using `C) R p := by`. Introduce `j`. Use `mem_pFun.1 (Submodule.sub_mem _ e1 e2) (b j)` as an intermediate fact. Simplify using `only [Pi.sub_apply, Phi_basis _ s (cut_supp s l)] at this`. Simplify `this` using `[cut]`.

Set `l2 : Fin n × Fin f → R` to `fun j => if j.2 = s then (if j.1 < i then 0 else if j.1 = i then c else l j) else 0`. Use `⟨l2, ?_, fun j hj => if_neg hj, fun j hj => by simp [l2, hj], by simp [l2]⟩` and prove the remaining obligations. Establish `e4 : cut s l - l2 ∈ afLatT p f b σ AA.carrier`. Use `mem_afLatT_of_p hinj _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨j, t⟩`.

Distinguish the cases in `ht : t = s`. Substitute `ht` using the available equality. Distinguish the cases in `hj : j < i`. Use `Submodule.sub_mem _ (h2 (b j) (Submodule.subset_span ⟨j, hj, rfl⟩)) (e3 j)` as an intermediate fact. Rewrite using `[← mem_pInt_iff hinj]`.

Simplify `this` using `[cut, l2, hj]`. Distinguish the cases in `hji : j = i`. Substitute `hji` using the available equality. Use `Submodule.sub_mem _ h3 (e3 j)` as an intermediate fact. Rewrite using `[← mem_pInt_iff hinj]`.

Simplify `this` using `[cut, l2]`. Simplify using `[cut, l2, hj, hji]`. Simplify using `[cut, l2, ht]`. Simplify using `using Submodule.sub_mem _ (hgrade l hlL s) e4`. Introduce and unpack `⟨l, hl, hs, hlow, rfl⟩`.

Take `⟨g, hg, hh⟩` from `haf l hl`. Rewrite `hh` using `[mem_pFun]`. Use `⟨g, hg, fun a x => ?_, fun k hk => ?_, ?_⟩` and prove the remaining obligations. Use `Submodule.sub_mem _ (hh (a • x)) (Submodule.smul_mem _ ((σ ^ p ^ (s : ℕ)) a) (hh x))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [Pi.sub_apply, Phi_eigen l s hs, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Use `hh k` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, Phi_flag l i ?_ k hk, sub_zero]`. Conclude with `this`.

Introduce and unpack `⟨j, t⟩ hj`. Distinguish the cases in `ht : t = s`. Substitute `ht` using the available equality. Conclude with `hlow j hj`. Conclude with `hs _ ht`.

Use `hh (b i)` as an intermediate fact. Rewrite `this` using `[Pi.sub_apply, Phi_basis l s hs]`. Then use the resulting hypothesis.
-/
theorem aflatT : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), (afLatT p f b σ AA.carrier).FG ∧ Nonempty (AFQuot p AA.carrier ≃ₗ[R] ((Fin n × Fin f → R) ⧸ afLatT p f b σ AA.carrier)) ∧ (∀ l ∈ afLatT p f b σ AA.carrier, ∀ s : Fin f, (fun j => if j.2 = s then l j else 0) ∈ afLatT p f b σ AA.carrier) ∧ ∀ (i : Fin n) (s : Fin f) (c : R), c ∈ idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) ↔ ∃ l ∈ afLatT p f b σ AA.carrier, (∀ j, j.2 ≠ s → l j = 0) ∧ (∀ j, j < i → l (j, s) = 0) ∧ l (i, s) = c := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hst σ hσ n b
  haveI : IsDomain R := hv.hom_inj.isDomain
  haveI : ValuationRing R := ValuationRing.of_integers v hv
  obtain ⟨h0, w, hw⟩ := exists_inv_card hv hp hc
  have hinj := hv.hom_inj
  have hdist := fund_pow_inj p v R hv hp F f hc σ hσ
  have hgrade : ∀ l ∈ afLatT p f b σ AA.carrier, ∀ s : Fin f,
      cut s l ∈ afLatT p f b σ AA.carrier := by
    intro l hl s
    rw [mem_afLatT, ← proj_Phi h0 hdist]
    exact proj_mem hw _ _ _ (sup_stable hst (mem_afLatT.1 hl))
  have haf : ∀ l ∈ afLatT p f b σ AA.carrier,
      ∃ g ∈ afFun p AA.carrier, g - Phi C p f b σ l ∈ pFun R p N := by
    intro l hl
    obtain ⟨g, hg, h, hh, e⟩ := Submodule.mem_sup.1 (mem_afLatT.1 hl)
    refine ⟨g, ⟨hg, ?_⟩, ?_⟩
    · rw [eq_sub_of_add_eq e]
      exact Submodule.sub_mem _ (Phi_mem_linFun hinj hσ l).2 (pFun_le_addFun hh)
    · rw [← e]
      simpa using Submodule.neg_mem _ hh
  refine ⟨?_, ?_, hgrade, fun i s c => ⟨?_, ?_⟩⟩
  · let ι : (N → R) →ₗ[R] (N → C) := (Algebra.linearMap R C).compLeft N
    have hι : Function.Injective ι := fun x y h => funext fun k => hinj (congrFun h k)
    let Φ : (Fin n × Fin f → R) →ₗ[R] (N → R) := Fintype.linearCombination R
      fun (j : Fin n × Fin f) (x : N) => (σ ^ p ^ (j.2 : ℕ)) (b.repr x j.1)
    have hΦ : Phi C p f b σ = ι ∘ₗ Φ := by
      refine LinearMap.ext fun l => funext fun x => ?_
      rw [Phi_apply]
      simp [ι, Φ, Fintype.linearCombination_apply, Finset.sum_apply]
    have hfg : (AA.carrier ⊔ pFun R p N).FG := by
      refine Submodule.FG.sup ?_ (Submodule.fg_pi fun _ => Submodule.fg_span_singleton _)
      obtain ⟨B, -, hB⟩ := AA.lat
      rw [hB]
      exact Submodule.fg_span (Set.finite_range _)
    have hle : AA.carrier ⊔ pFun R p N ≤ LinearMap.range ι := by
      have hint : intFun R N ≤ LinearMap.range ι := by
        intro g hg
        choose r hr using hg
        exact ⟨r, funext hr⟩
      refine le_trans (sup_le AA.le_int fun g hg x => ?_) hint
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (mem_pFun.1 hg x)
      exact ⟨c * p, by rw [← hc, Algebra.smul_def, map_mul, map_natCast]⟩
    have h1 : ((AA.carrier ⊔ pFun R p N).comap ι).FG :=
      Submodule.fg_of_fg_map_injective ι hι (by rw [Submodule.map_comap_eq_self hle]; exact hfg)
    have h2 := comap_fg_of_valuationRing R _ _ Φ _ h1
    rw [← Submodule.comap_comp, ← hΦ] at h2
    exact h2
  · let Φ : (Fin n × Fin f → R) →ₗ[R] linFun (C := C) R p N :=
      (Phi C p f b σ).codRestrict _ (Phi_mem_linFun hinj hσ)
    let θ : (Fin n × Fin f → R) →ₗ[R] AFQuot p AA.carrier := Submodule.mkQ _ ∘ₗ Φ
    have hsurj : Function.Surjective θ := by
      intro q
      obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨l, hl⟩ := exists_Phi p hv hp hc hσ b g.2
      refine ⟨l, ((Submodule.Quotient.eq _).2 ?_).symm⟩
      exact Submodule.mem_sup_right hl
    have hker : LinearMap.ker θ = afLatT p f b σ AA.carrier := by
      ext l
      have : l ∈ LinearMap.ker θ ↔ Phi C p f b σ l ∈ afFun p AA.carrier ⊔ pFun R p N :=
        Submodule.Quotient.mk_eq_zero _
      rw [this]
      constructor
      · intro h
        have hle : afFun p AA.carrier ⊔ pFun R p N ≤ AA.carrier ⊔ pFun R p N :=
          sup_le_sup_right (fun _ hx => hx.1) _
        exact mem_afLatT.2 (hle h)
      · intro h
        obtain ⟨g, hg, hh⟩ := haf l h
        have := Submodule.sub_mem _ (Submodule.mem_sup_left (T := pFun R p N) hg)
          (Submodule.mem_sup_right hh)
        simpa using this
    exact ⟨(θ.quotKerEquivOfSurjective hsurj).symm.trans (Submodule.quotEquivOfEq _ _ hker)⟩
  · rintro ⟨g, hg, h1, h2, h3⟩
    obtain ⟨l, hl⟩ := exists_Phi p hv hp hc hσ b (g := g) ⟨AA.le_int hg.1, hg.2⟩
    have hlL : l ∈ afLatT p f b σ AA.carrier := by
      have := Submodule.sub_mem _ (Submodule.mem_sup_left (T := pFun R p N) hg.1)
        (Submodule.mem_sup_right hl)
      rw [mem_afLatT]
      simpa using this
    have e1 : proj (σ ^ p ^ (s : ℕ)) g - Phi C p f b σ (cut s l) ∈ pFun R p N := by
      rw [← proj_Phi h0 hdist, ← projL_apply, ← projL_apply, ← map_sub]
      exact proj_mem hw _ _ _ fun a => mem_pFun.2 fun x => mem_pFun.1 hl _
    have e2 : proj (σ ^ p ^ (s : ℕ)) g - g ∈ pFun R p N := by
      rw [mem_pFun]
      intro x
      have := Submodule.smul_mem _ w (Submodule.sum_mem _ (t := Finset.univ) fun (a : Fˣ) _ =>
        Submodule.smul_mem _ ((σ ^ p ^ (s : ℕ))⁻¹ (a : F)) (h1 a x))
      convert this using 1
      simp only [Algebra.smul_def, mul_sub, Finset.sum_sub_distrib, ← mul_assoc, ← map_mul,
        inv_mul_apply, hw, Pi.sub_apply, proj]
      simp [h0]
    have e3 : ∀ j, g (b j) - algebraMap R C (l (j, s)) ∈ pInt (C := C) R p := by
      intro j
      have := mem_pFun.1 (Submodule.sub_mem _ e1 e2) (b j)
      simp only [Pi.sub_apply, Phi_basis _ s (cut_supp s l)] at this
      simpa [cut] using this
    let l2 : Fin n × Fin f → R := fun j =>
      if j.2 = s then (if j.1 < i then 0 else if j.1 = i then c else l j) else 0
    refine ⟨l2, ?_, fun j hj => if_neg hj, fun j hj => by simp [l2, hj], by simp [l2]⟩
    have e4 : cut s l - l2 ∈ afLatT p f b σ AA.carrier := by
      refine mem_afLatT_of_p hinj _ _ ?_
      rintro ⟨j, t⟩
      by_cases ht : t = s
      · subst ht
        by_cases hj : j < i
        · have := Submodule.sub_mem _
            (h2 (b j) (Submodule.subset_span ⟨j, hj, rfl⟩)) (e3 j)
          rw [← mem_pInt_iff hinj]
          simpa [cut, l2, hj] using this
        · by_cases hji : j = i
          · subst hji
            have := Submodule.sub_mem _ h3 (e3 j)
            rw [← mem_pInt_iff hinj]
            simpa [cut, l2] using this
          · simp [cut, l2, hj, hji]
      · simp [cut, l2, ht]
    simpa using Submodule.sub_mem _ (hgrade l hlL s) e4
  · rintro ⟨l, hl, hs, hlow, rfl⟩
    obtain ⟨g, hg, hh⟩ := haf l hl
    rw [mem_pFun] at hh
    refine ⟨g, hg, fun a x => ?_, fun k hk => ?_, ?_⟩
    · have := Submodule.sub_mem _ (hh (a • x))
        (Submodule.smul_mem _ ((σ ^ p ^ (s : ℕ)) a) (hh x))
      convert this using 1
      simp only [Pi.sub_apply, Phi_eigen l s hs, Algebra.smul_def]
      ring
    · have := hh k
      rw [Pi.sub_apply, Phi_flag l i ?_ k hk, sub_zero] at this
      · exact this
      · rintro ⟨j, t⟩ hj
        by_cases ht : t = s
        · subst ht
          exact hlow j hj
        · exact hs _ ht
    · have := hh (b i)
      rwa [Pi.sub_apply, Phi_basis l s hs] at this

/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hst σ hσ n b`. Take `⟨hfg, ⟨e⟩, hgr, hD⟩` from `aflatT p C v R hv hp F f hc N AA hst σ hσ n b`. Use `set L := afLatT p f b σ AA.carrier with hL`. Set `ρ : Fin f → (Fin n × Fin f → R) →ₗ[R] (Fin n → R)` to `fun s => LinearMap.funLeft R R fun j => (j, s)`. Use `choose d hd hlen using fun s => triang_strong C v R hv n (L.map (ρ s)) (hfg.map _)`.

Use `⟨fun i s => d s i, fun i s => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `c`. Rewrite using `[hD, hd]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨l, hl, -, h2, h3⟩`.

Conclude with `⟨ρ s l, Submodule.mem_map_of_mem hl, h2, h3⟩`. Introduce and unpack `⟨_, ⟨l, hl, rfl⟩, h2, h3⟩`. Conclude with `⟨_, hgr l hl s, fun j hj => if_neg hj, fun j hj => (if_pos rfl).trans (h2 j hj), (if_pos rfl).trans h3⟩`. Set `θ : (Fin n × Fin f → R) →ₗ[R] ((s : Fin f) → (Fin n → R) ⧸ L.map (ρ s))` to `LinearMap.pi fun s => Submodule.mkQ _ ∘ₗ ρ s`. Establish `hsurj : Function.Surjective θ`.

Introduce `q`. Use `choose u hu using fun s => Submodule.Quotient.mk_surjective _ (q s)`. Conclude with `⟨fun j => u j.2 j.1, funext hu⟩`. Establish `hker : LinearMap.ker θ = L`. Use extensionality with `l`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← sum_cut l]`. Use `L.sum_mem fun s _ => ?_` and prove the remaining obligations. Take `⟨l', hl', e'⟩ : ρ s l ∈ L.map (ρ s)` from `(Submodule.Quotient.mk_eq_zero _).1 (congrFun (LinearMap.mem_ker.1 h) s)`.

Establish `: cut s l = cut s l'`. Use function extensionality and compare the values at `⟨j, t⟩`. Distinguish the cases in `ht : t = s`. Substitute `ht` using the available equality. Simplify `(congrFun e' j).symm` using `[cut, ρ]`.

Simplify using `[cut, ht]`. Rewrite using `[this]`. Conclude with `hgr l' hl' s`. Introduce `h`. Use function extensionality and compare the values at `s`.

Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_map_of_mem h)`. Rewrite using `[Finset.prod_comm]`. Conclude with `Tot.hasLen_equiv (e.trans ((Submodule.quotEquivOfEq _ _ hker).symm.trans (θ.quotKerEquivOfSurjective hsurj))) (Tot.hasLen_pi _ _ hlen)`.
-/
theorem flag_D : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ (n : ℕ) (b : Module.Basis (Fin n) F N), ∃ d : Fin n → Fin f → R, (∀ (i : Fin n) (s : Fin f), idealD p AA.carrier (flagSub b i) (b i) (σ ^ p ^ (s : ℕ)) = Ideal.span {d i s}) ∧ HasLen v R (AFQuot p AA.carrier) (∏ i, ∏ s, v (algebraMap R C (d i s))) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc N _ _ _ _ AA hst σ hσ n b
  obtain ⟨hfg, ⟨e⟩, hgr, hD⟩ := aflatT p C v R hv hp F f hc N AA hst σ hσ n b
  set L := afLatT p f b σ AA.carrier with hL
  let ρ : Fin f → (Fin n × Fin f → R) →ₗ[R] (Fin n → R) := fun s =>
    LinearMap.funLeft R R fun j => (j, s)
  choose d hd hlen using fun s => triang_strong C v R hv n (L.map (ρ s)) (hfg.map _)
  refine ⟨fun i s => d s i, fun i s => ?_, ?_⟩
  · ext c
    rw [hD, hd]
    constructor
    · rintro ⟨l, hl, -, h2, h3⟩
      exact ⟨ρ s l, Submodule.mem_map_of_mem hl, h2, h3⟩
    · rintro ⟨_, ⟨l, hl, rfl⟩, h2, h3⟩
      exact ⟨_, hgr l hl s, fun j hj => if_neg hj, fun j hj => (if_pos rfl).trans (h2 j hj),
        (if_pos rfl).trans h3⟩
  · let θ : (Fin n × Fin f → R) →ₗ[R] ((s : Fin f) → (Fin n → R) ⧸ L.map (ρ s)) :=
      LinearMap.pi fun s => Submodule.mkQ _ ∘ₗ ρ s
    have hsurj : Function.Surjective θ := by
      intro q
      choose u hu using fun s => Submodule.Quotient.mk_surjective _ (q s)
      exact ⟨fun j => u j.2 j.1, funext hu⟩
    have hker : LinearMap.ker θ = L := by
      ext l
      constructor
      · intro h
        rw [← sum_cut l]
        refine L.sum_mem fun s _ => ?_
        obtain ⟨l', hl', e'⟩ : ρ s l ∈ L.map (ρ s) :=
          (Submodule.Quotient.mk_eq_zero _).1 (congrFun (LinearMap.mem_ker.1 h) s)
        have : cut s l = cut s l' := by
          funext ⟨j, t⟩
          by_cases ht : t = s
          · subst ht
            simpa [cut, ρ] using (congrFun e' j).symm
          · simp [cut, ht]
        rw [this]
        exact hgr l' hl' s
      · intro h
        funext s
        exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_map_of_mem h)
    rw [Finset.prod_comm]
    exact Tot.hasLen_equiv
      (e.trans ((Submodule.quotEquivOfEq _ _ hker).symm.trans (θ.quotKerEquivOfSurjective hsurj)))
      (Tot.hasLen_pi _ _ hlen)

end PositivityTheory.HtPt.Rb
