import Mathlib
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.WeightDictionaryLifting
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause

noncomputable section

namespace GlobalTheory.Cmp.JumpDict

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Cmp.SmallJumps

section Split

variable {Qp K LL M : Type} [Field Qp] [Field K] [Field LL] [Algebra Qp K] [Algebra Qp LL]
  [AddCommGroup M] [Module LL M] [Module Qp M] [IsScalarTower Qp LL M] [FiniteDimensional Qp K]

/- English proof (translation)
Set `Φ : LL ⊗[Qp] K →ₐ[LL] ((K →ₐ[Qp] LL) → LL)` to `Pi.algHom _ _ fun τ => Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => Commute.all _ _`. Establish `hΦ : ∀ (a : LL) (c : K) τ, Φ (a ⊗ₜ c) τ = a * τ c` using `fun a c τ => by simp [Φ]`. Establish `hsurj : Function.Surjective Φ`. Establish `hli : LinearIndependent LL (fun τ : K →ₐ[Qp] LL => (τ : K → LL))` using `(linearIndependent_monoidHom K LL).comp (fun τ : K →ₐ[Qp] LL => (τ : K →* LL)) (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)`. Establish `hsp` using `span_flip_eq_top_iff_linearIndependent.2 hli`.

Establish `: LinearMap.range Φ.toLinearMap = ⊤`. Rewrite using `[eq_top_iff, ← hsp, Submodule.span_le]`. Introduce and unpack `_ ⟨c, rfl⟩`. Conclude with `⟨1 ⊗ₜ c, funext fun τ => by simp [hΦ, flip]⟩`. Conclude with `LinearMap.range_eq_top.1 this`.

Establish `hinj : Function.Injective Φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap) (by`. Simplify using `[hcard])).2 hsurj`. Set `Ψ : LL ⊗[Qp] K →ₐ[LL] Module.End LL M` to `Algebra.TensorProduct.lift (Algebra.ofId LL _) m fun a c => Algebra.commutes a (m c)`. Establish `hΨ : ∀ (a : LL) (c : K) x, Ψ (a ⊗ₜ c) x = a • m c x` using `fun a c x => (LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId LL _) m (fun a c => Algebra.commutes a (m c)) a c) x).trans (by simp)`. Establish `hΨU : ∀ z, ∀ x ∈ U, Ψ z x ∈ U`.

Introduce `z x hx`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a c => rw [hΨ]`. Conclude with `U.smul_mem _ (hU c x hx)`.

Consider the case `add y z hy hz => rw [map_add]`. Conclude with `U.add_mem hy hz`. Establish `hΨE : ∀ τ z, ∀ x ∈ E τ, Ψ z x = Φ z τ • x`. Introduce `τ z x hx`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul a c => rw [hΨ, hΦ, ((hE τ x).1 hx).2 c, smul_smul]`. Consider the case `add y z hy hz => simp only [map_add, LinearMap.add_apply, Pi.add_apply, hy, hz, add_smul]`. Use `choose e he using fun τ : K →ₐ[Qp] LL => hsurj (Pi.single τ 1)`. Establish `he1 : ∑ τ, e τ = 1` using `hinj (by`.

Rewrite using `[map_sum, map_one]`. Simplify using `only [he]`. Conclude with `Finset.univ_sum_single (fun _ => (1 : LL)))`. Establish `he2 : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ` using `fun τ c => hinj (by`. Rewrite using `[map_mul, map_smul, he]`.

Use function extensionality and compare the values at `σ`. Distinguish the cases in `h : σ = τ`. Substitute `h` using the available equality. Simplify using `[hΦ]`. Simplify using `[h])`.

Establish `hmem : ∀ τ, ∀ x ∈ U, Ψ (e τ) x ∈ E τ` using `fun τ x hx => (hE τ _).2 ⟨hΨU _ x hx, fun c => by`. Use `congrArg (fun z => Ψ z x) (he2 τ c)` as an intermediate fact. Simplify `this⟩` using `only [map_mul, map_smul, Module.End.mul_apply, hΨ, one_smul, LinearMap.smul_apply]`. Set `f : U ≃ₗ[LL] (∀ τ, E τ)` to `{ toFun := fun x τ => ⟨Ψ (e τ) x, hmem τ x x.2⟩ map_add' := fun x y => funext fun τ => Subtype.ext (by simp) map_smul' := fun a x => funext fun τ => Subtype.ext (by simp) invFun := fun y => ⟨∑ τ, (y τ : M), U.sum_mem fun τ _ => ((hE τ _).1 (y τ).2).1⟩ left_inv := fun x => Subtype …`. Express the relevant statement in the definitionally equal form `∑ τ, Ψ (e τ) x = x`.

Rewrite using `[← LinearMap.sum_apply, ← map_sum, he1, map_one, Module.End.one_apply])`. Use `right_inv := fun y => funext fun τ => Subtype.ext (by`. Express the relevant statement in the definitionally equal form `Ψ (e τ) (∑ σ, (y σ : M)) = y τ`. Rewrite using `[map_sum, Finset.sum_eq_single τ]`. Rewrite using `[hΨE τ _ _ (y τ).2, he]`.

Simplify using the standard rewrite rules. Introduce `σ _ h`. Rewrite using `[hΨE σ _ _ (y σ).2, he]`. Simplify using `[h]`. Use the proof step `simp) }`.

Rewrite using `[f.finrank_eq, Module.finrank_pi_fintype]`.
-/
theorem finrank_eq_sum_emb (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (m : K →ₐ[Qp] Module.End LL M) (U : Submodule LL M) (hU : ∀ c, ∀ x ∈ U, m c x ∈ U)
    (E : (K →ₐ[Qp] LL) → Submodule LL M) (hE : ∀ τ x, x ∈ E τ ↔ x ∈ U ∧ ∀ c, m c x = τ c • x)
    [∀ τ, FiniteDimensional LL (E τ)] : finrank LL U = ∑ τ, finrank LL (E τ) := by
  classical
  let Φ : LL ⊗[Qp] K →ₐ[LL] ((K →ₐ[Qp] LL) → LL) :=
    Pi.algHom _ _ fun τ => Algebra.TensorProduct.lift (AlgHom.id LL LL) τ fun _ _ => Commute.all _ _
  have hΦ : ∀ (a : LL) (c : K) τ, Φ (a ⊗ₜ c) τ = a * τ c := fun a c τ => by simp [Φ]
  have hsurj : Function.Surjective Φ := by
    have hli : LinearIndependent LL (fun τ : K →ₐ[Qp] LL => (τ : K → LL)) :=
      (linearIndependent_monoidHom K LL).comp (fun τ : K →ₐ[Qp] LL => (τ : K →* LL))
        (fun a b h => AlgHom.ext fun x => DFunLike.congr_fun h x)
    have hsp := span_flip_eq_top_iff_linearIndependent.2 hli
    have : LinearMap.range Φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hsp, Submodule.span_le]
      rintro _ ⟨c, rfl⟩
      exact ⟨1 ⊗ₜ c, funext fun τ => by simp [hΦ, flip]⟩
    exact LinearMap.range_eq_top.1 this
  have hinj : Function.Injective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := Φ.toLinearMap) (by
      simp [hcard])).2 hsurj
  let Ψ : LL ⊗[Qp] K →ₐ[LL] Module.End LL M :=
    Algebra.TensorProduct.lift (Algebra.ofId LL _) m fun a c => Algebra.commutes a (m c)
  have hΨ : ∀ (a : LL) (c : K) x, Ψ (a ⊗ₜ c) x = a • m c x := fun a c x =>
    (LinearMap.congr_fun (Algebra.TensorProduct.lift_tmul (Algebra.ofId LL _) m
      (fun a c => Algebra.commutes a (m c)) a c) x).trans (by simp)
  have hΨU : ∀ z, ∀ x ∈ U, Ψ z x ∈ U := by
    intro z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ]; exact U.smul_mem _ (hU c x hx)
    | add y z hy hz => rw [map_add]; exact U.add_mem hy hz
  have hΨE : ∀ τ z, ∀ x ∈ E τ, Ψ z x = Φ z τ • x := by
    intro τ z x hx
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => rw [hΨ, hΦ, ((hE τ x).1 hx).2 c, smul_smul]
    | add y z hy hz => simp only [map_add, LinearMap.add_apply, Pi.add_apply, hy, hz, add_smul]
  choose e he using fun τ : K →ₐ[Qp] LL => hsurj (Pi.single τ 1)
  have he1 : ∑ τ, e τ = 1 := hinj (by
    rw [map_sum, map_one]
    simp only [he]
    exact Finset.univ_sum_single (fun _ => (1 : LL)))
  have he2 : ∀ τ c, (1 ⊗ₜ c) * e τ = τ c • e τ := fun τ c => hinj (by
    rw [map_mul, map_smul, he]
    funext σ
    by_cases h : σ = τ
    · subst h; simp [hΦ]
    · simp [h])
  have hmem : ∀ τ, ∀ x ∈ U, Ψ (e τ) x ∈ E τ := fun τ x hx =>
    (hE τ _).2 ⟨hΨU _ x hx, fun c => by
      have := congrArg (fun z => Ψ z x) (he2 τ c)
      simpa only [map_mul, map_smul, Module.End.mul_apply, hΨ, one_smul, LinearMap.smul_apply] using this⟩
  let f : U ≃ₗ[LL] (∀ τ, E τ) :=
    { toFun := fun x τ => ⟨Ψ (e τ) x, hmem τ x x.2⟩
      map_add' := fun x y => funext fun τ => Subtype.ext (by simp)
      map_smul' := fun a x => funext fun τ => Subtype.ext (by simp)
      invFun := fun y => ⟨∑ τ, (y τ : M), U.sum_mem fun τ _ => ((hE τ _).1 (y τ).2).1⟩
      left_inv := fun x => Subtype.ext (by
        change ∑ τ, Ψ (e τ) x = x
        rw [← LinearMap.sum_apply, ← map_sum, he1, map_one, Module.End.one_apply])
      right_inv := fun y => funext fun τ => Subtype.ext (by
        change Ψ (e τ) (∑ σ, (y σ : M)) = y τ
        rw [map_sum, Finset.sum_eq_single τ]
        · rw [hΨE τ _ _ (y τ).2, he]; simp
        · intro σ _ h
          rw [hΨE σ _ _ (y σ).2, he]; simp [h]
        · simp) }
  rw [f.finrank_eq, Module.finrank_pi_fintype]

end Split

/- English proof (translation)
Establish `hA : Antitone F` using `antitone_int_of_succ_le anti`. Use `haveI : ∀ a, FiniteDimensional L (F a) := fun a => Submodule.finiteDimensional_of_le (le a)`. Establish `hs : ∀ a, a ≠ a₀ → F (a + 1) = F a` using `fun a ha => Submodule.eq_of_le_of_finrank_eq (anti a) (by have := h a; rw [if_neg ha] at this; omega)`. Establish `hlo : ∀ a ≤ a₀, F a = F a₀`. Introduce `a ha`.

Proceed by induction on `a, ha using Int.le_induction_down with`. Consider the case `base => rfl`. Consider the case `pred a ha ih => rw [← ih, ← hs (a - 1) (by omega), sub_add_cancel]`. Establish `hhi : ∀ a, a₀ + 1 ≤ a → F a = F (a₀ + 1)`. Introduce `a ha`.

Proceed by induction on `a, ha using Int.le_induction with`. Consider the case `base => rfl`. Consider the case `succ a ha ih => rw [← ih, hs a (by omega)]`. Establish `h1 : U = F a₀` using `le_antisymm (fun x hx => by`. Take `⟨a, ha⟩` from `exh x hx`.

Break down `le_total a a₀ with hab | hab` into its components or cases. Rewrite using `[← hlo a hab]` and apply the resulting hypothesis. Conclude with `hA hab ha) (le _)`. Establish `h2 : F (a₀ + 1) = ⊥` using `eq_bot_iff.2 fun x hx => sep x fun a => by`. Break down `le_total a (a₀ + 1) with hab | hab` into its components or cases.

Conclude with `hA hab hx`. Rewrite using `[hhi a hab]` and apply the resulting hypothesis. Establish `h3` using `h a₀`. Rewrite `h3` using `[h2, if_pos rfl, finrank_bot]`. Rewrite using `[h1]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_eq_one_of_jump {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) [FiniteDimensional L U] (le : ∀ a, F a ≤ U) (anti : ∀ a, F (a + 1) ≤ F a)
    (exh : ∀ x ∈ U, ∃ a, x ∈ F a) (sep : ∀ x, (∀ a, x ∈ F a) → x = 0) (a₀ : ℤ)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = if a = a₀ then 1 else 0) :
    finrank L U = 1 := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  haveI : ∀ a, FiniteDimensional L (F a) := fun a => Submodule.finiteDimensional_of_le (le a)
  have hs : ∀ a, a ≠ a₀ → F (a + 1) = F a := fun a ha =>
    Submodule.eq_of_le_of_finrank_eq (anti a) (by have := h a; rw [if_neg ha] at this; omega)
  have hlo : ∀ a ≤ a₀, F a = F a₀ := by
    intro a ha
    induction a, ha using Int.le_induction_down with
    | base => rfl
    | pred a ha ih => rw [← ih, ← hs (a - 1) (by omega), sub_add_cancel]
  have hhi : ∀ a, a₀ + 1 ≤ a → F a = F (a₀ + 1) := by
    intro a ha
    induction a, ha using Int.le_induction with
    | base => rfl
    | succ a ha ih => rw [← ih, hs a (by omega)]
  have h1 : U = F a₀ := le_antisymm (fun x hx => by
    obtain ⟨a, ha⟩ := exh x hx
    rcases le_total a a₀ with hab | hab
    · rwa [← hlo a hab]
    · exact hA hab ha) (le _)
  have h2 : F (a₀ + 1) = ⊥ := eq_bot_iff.2 fun x hx => sep x fun a => by
    rcases le_total a (a₀ + 1) with hab | hab
    · exact hA hab hx
    · rwa [hhi a hab]
  have h3 := h a₀
  rw [h2, if_pos rfl, finrank_bot] at h3
  rw [h1]
  omega

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

/- English proof (translation)
Set `b` to `Module.Basis.ofVectorSpace Qp V`. Apply `(equivFinsuppOfBasisLeft (N := BdR) b).injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Use extensionality with `i`. Use `PD.Fil_sep _ fun a => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `hx a`. Use `clear hx`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v c`.

Establish `: (equivFinsuppOfBasisLeft (N` using `BdR) b) (v ⊗ₜ (c : BdR)) i ∈ PD.Fil a := by`. Rewrite using `[equivFinsuppOfBasisLeft_apply_tmul_apply]`. Conclude with `((PD.Fil a).restrictScalars Qp).smul_mem _ c.2`. Conclude with `this`. Consider the case `add y z hy hz => rw [map_add, map_add, Finsupp.add_apply]`.

Conclude with `Submodule.add_mem _ hy hz`.
-/
theorem filV_sep (x : V ⊗[Qp] BdR) (hx : ∀ a, x ∈ FilV PD (LL := LL) (V := V) a) : x = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace Qp V
  apply (equivFinsuppOfBasisLeft (N := BdR) b).injective
  rw [map_zero]
  ext i
  refine PD.Fil_sep _ fun a => ?_
  obtain ⟨y, rfl⟩ := hx a
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v c =>
    have : (equivFinsuppOfBasisLeft (N := BdR) b) (v ⊗ₜ (c : BdR)) i ∈ PD.Fil a := by
      rw [equivFinsuppOfBasisLeft_apply_tmul_apply]
      exact ((PD.Fil a).restrictScalars Qp).smul_mem _ c.2
    exact this
  | add y z hy hz => rw [map_add, map_add, Finsupp.add_apply]; exact Submodule.add_mem _ hy hz

/- English proof (translation)
Use `choose a₀ h using h`. Use `haveI : ∀ τ, FiniteDimensional LL (DdRE PD ρ τ) := fun τ => finite_ddRE_of_multV PD ρ τ {a₀ τ} (by simp) fun a => by`. Apply the tactic sequence `rw [h, Multiset.count_singleton]; split_ifs <;> rfl`. Establish `h1 : ∀ τ, finrank LL (DdRE PD ρ τ) = 1` using `fun τ => finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left) (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1))) (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) (a₀ τ) (h τ)`. Establish `hm : ∀ (c : K) (v : V) (b : BdR), mulVdR (K` using `K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) := fun _ _ _ => rfl`.

Set `m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR)` to `{ toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c map_one' := by ext v b; simp [hm] map_mul' := fun c d => by ext v b; simp [hm, mul_assoc] map_zero' := by ext v b; simp [hm] map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add] commutes' := fun r = …`. Use extensionality with `v b`. Simplify using `[hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }`. Establish `hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x` using `fun x => by`. Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`.

Establish `hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x)`. Introduce `g c x`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v b => simp [m, hm, actVdR]`.

Consider the case `add y z hy hz => simp only [map_add, hy, hz]`. Rewrite using `[finrank_eq_sum_emb hcard m (DdR PD ρ) (fun c x hx => (hD _).2 fun g => by rw [hc, (hD x).1 hx g]) (DdRE PD ρ) (fun τ x => by`. Simplify using `only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Use the proof step `rfl)]`. Simplify using `[h1, hcard]`.
-/
theorem finrank_ddR_of_one_jump [FiniteDimensional Qp K] (hcard : Fintype.card (K →ₐ[Qp] LL) = finrank Qp K)
    (ρ : Representation LL G V)
    (h : ∀ τ : K →ₐ[Qp] LL, ∃ a₀ : ℤ, ∀ a, multV PD ρ τ a = if a = a₀ then 1 else 0) :
    finrank LL (DdR PD ρ) = finrank Qp K := by
  choose a₀ h using h
  haveI : ∀ τ, FiniteDimensional LL (DdRE PD ρ τ) := fun τ =>
    finite_ddRE_of_multV PD ρ τ {a₀ τ} (by simp) fun a => by
      rw [h, Multiset.count_singleton]; split_ifs <;> rfl
  have h1 : ∀ τ, finrank LL (DdRE PD ρ τ) = 1 := fun τ =>
    finrank_eq_one_of_jump (FildR PD ρ τ) _ (fun _ => inf_le_left)
      (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
      (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩)
      (fun x hx => filV_sep PD (LL := LL) x fun a => (hx a).2) (a₀ τ) (h τ)
  have hm : ∀ (c : K) (v : V) (b : BdR),
      mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) (Qp := Qp) c (v ⊗ₜ b) = v ⊗ₜ (algebraMap K BdR c * b) :=
    fun _ _ _ => rfl
  let m : K →ₐ[Qp] Module.End LL (V ⊗[Qp] BdR) :=
    { toFun := fun c => mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
      map_one' := by ext v b; simp [hm]
      map_mul' := fun c d => by ext v b; simp [hm, mul_assoc]
      map_zero' := by ext v b; simp [hm]
      map_add' := fun c d => by ext v b; simp [hm, add_mul, tmul_add]
      commutes' := fun r => by
        ext v b
        simp [hm, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def, Algebra.algebraMap_eq_smul_one] }
  have hD : ∀ x, x ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g x = x := fun x => by
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
  have hc : ∀ g c x, actVdR PD ρ g (m c x) = m c (actVdR PD ρ g x) := by
    intro g c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [m, hm, actVdR]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [finrank_eq_sum_emb hcard m (DdR PD ρ) (fun c x hx => (hD _).2 fun g => by rw [hc, (hD x).1 hx g])
    (DdRE PD ρ) (fun τ x => by
      simp only [DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      rfl)]
  simp [h1, hcard]

end Periods

variable (D : D7)

/- English proof (translation)
The claim follows from `RingHom.ext fun x => D.host.conjE_apply (WeightDictionaryLifting.embOf D ρ) x`.
-/
theorem embOver_true (ρ : D.what₂.Tau) :
    JumpDictionary.embOver D ρ true = (starRingEnd ℂ).comp (WeightDictionaryLifting.embOf D ρ) :=
  RingHom.ext fun x => D.host.conjE_apply (WeightDictionaryLifting.embOf D ρ) x

/- English proof (translation)
The claim follows from `RingHom.ext fun x => by simp`.
-/
theorem conj_conj (φ : D.host.E →+* ℂ) : (starRingEnd ℂ).comp ((starRingEnd ℂ).comp φ) = φ :=
  RingHom.ext fun x => by simp

/- English proof (translation)
Establish `h0 : D.host.φ₀ (D.host.sqd) = _` using `D.host.φ₀_mem`. Establish `hd : (0 : ℝ) < Real.sqrt D.host.d` using `Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)`. Establish `hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ)`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Simplify using the standard rewrite rules.

Establish `h1 : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E)` using `D.host.φ₀.injective (by rw [map_pow, h0, mul_pow, hs, map_neg, map_natCast]; simp)`. Establish `h2 : φ (D.host.sqd) ^ 2 = (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2`. Rewrite using `[← map_pow, h1, mul_pow, hs, map_neg, map_natCast]`. Simplify using the standard rewrite rules. Simplify using `only [Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.comp_apply]`.

Establish `hne : Complex.I * (Real.sqrt D.host.d : ℂ) ≠ -(Complex.I * (Real.sqrt D.host.d : ℂ))` using `fun h => by`. Use `congrArg Complex.im h` as an intermediate fact. Simplify using `only [Complex.neg_im, Complex.I_mul_im, Complex.ofReal_re] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hc : starRingEnd ℂ (Complex.I * (Real.sqrt D.host.d : ℂ)) = -(Complex.I * (Real.sqrt D.host.d : ℂ))`.

Rewrite using `[map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h` into its components or cases. Rewrite using `[h, hc]`. Conclude with `⟨fun h' => absurd h'.symm hne, fun h' => absurd rfl h'⟩`. Rewrite using `[h, map_neg, hc, neg_neg]`.

Conclude with `⟨fun _ h' => hne h'.symm, fun _ => rfl⟩`.
-/
theorem conj_mem_iff (φ : D.host.E →+* ℂ) :
    (starRingEnd ℂ).comp φ ∈ D.host.cmType ↔
      φ ∉ D.host.cmType := by
  have h0 : D.host.φ₀ (D.host.sqd) = _ := D.host.φ₀_mem
  have hd : (0 : ℝ) < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast D.host.hyp.2.1.pos)
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have h1 : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) :=
    D.host.φ₀.injective (by rw [map_pow, h0, mul_pow, hs, map_neg, map_natCast]; simp)
  have h2 : φ (D.host.sqd) ^ 2 =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) ^ 2 := by
    rw [← map_pow, h1, mul_pow, hs, map_neg, map_natCast]; simp
  simp only [Formalism.HC.HostRaw.cmType, Set.mem_setOf_eq, RingHom.comp_apply]
  have hne : Complex.I * (Real.sqrt D.host.d : ℂ) ≠ -(Complex.I * (Real.sqrt D.host.d : ℂ)) := fun h => by
    have := congrArg Complex.im h
    simp only [Complex.neg_im, Complex.I_mul_im, Complex.ofReal_re] at this
    linarith
  have hc : starRingEnd ℂ (Complex.I * (Real.sqrt D.host.d : ℂ)) = -(Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h | h
  · rw [h, hc]
    exact ⟨fun h' => absurd h'.symm hne, fun h' => absurd rfl h'⟩
  · rw [h, map_neg, hc, neg_neg]
    exact ⟨fun _ h' => hne h'.symm, fun _ => rfl⟩

/- English proof (translation)
Establish `key : ∀ ψ ∈ D.host.cmType, ∃ ρ, ψ = WeightDictionaryLifting.embOf D ρ`. Introduce `ψ hψ`. Take `⟨g, rfl⟩` from `(factEmb D.R D.host).1.2 ψ`. Use `⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 hψ⟩, ?_⟩` and prove the remaining obligations. Simplify using `[WeightDictionaryLifting.embOf]`.

Distinguish the cases in `h : φ ∈ D.host.cmType`. Take `⟨ρ, hρ⟩` from `key φ h`. Conclude with `⟨ρ, false, hρ⟩`. Take `⟨ρ, hρ⟩` from `key _ ((conj_mem_iff D φ).2 h)`. Conclude with `⟨ρ, true, by rw [embOver_true, ← hρ, conj_conj]⟩`.
-/
theorem exists_embOver (φ : D.host.E →+* ℂ) : ∃ ρ b, φ = JumpDictionary.embOver D ρ b := by
  have key : ∀ ψ ∈ D.host.cmType, ∃ ρ, ψ = WeightDictionaryLifting.embOf D ρ := by
    intro ψ hψ
    obtain ⟨g, rfl⟩ := (factEmb D.R D.host).1.2 ψ
    refine ⟨D.eTau.symm ⟨g, ((factEmb D.R D.host).2 g).1 hψ⟩, ?_⟩
    simp [WeightDictionaryLifting.embOf]
  by_cases h : φ ∈ D.host.cmType
  · obtain ⟨ρ, hρ⟩ := key φ h
    exact ⟨ρ, false, hρ⟩
  · obtain ⟨ρ, hρ⟩ := key _ ((conj_mem_iff D φ).2 h)
    exact ⟨ρ, true, by rw [embOver_true, ← hρ, conj_conj]⟩

section Local

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Local

def EtaParam : Prop :=
  ∀ (_ : D.nd.Loc) (ρ : D.what₂.Tau),
    D.naut.infG D.naut.etaTinv (JumpDictionary.embOver D ρ false) = {-(1 / 2 : ℂ)} ∧
    D.naut.infG D.naut.etaTinv (JumpDictionary.embOver D ρ true) = {(1 / 2 : ℂ)}

section Family

variable {eps : ℝ} (Fm : FamP eps)

end Family

end GlobalTheory.Cmp.JumpDict

end
