import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

noncomputable section

namespace GlobalTheory.NL.Points

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use `⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (AlgHom.normal_bijective _ _ _ _), fun x => ?_⟩` and prove the remaining obligations. Conclude with `f.liftNormal_commutes (Om l) x`.
-/
theorem exists_aut (F : IntermediateField ℚ_[l] (Om l)) (f : ↥F →ₐ[ℚ_[l]] Om l) :
    ∃ g : GQ l, ∀ x : ↥F, g (x : Om l) = f x := by
  refine ⟨AlgEquiv.ofBijective (f.liftNormal (Om l)) (AlgHom.normal_bijective _ _ _ _), fun x => ?_⟩
  exact f.liftNormal_commutes (Om l) x

/- English proof (translation)
Assemble the required witnesses or components as `⟨(g.toAlgHom.comp F.val).codRestrict LL.1.toSubalgebra (fun x => h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨x, hF x.2⟩), fun _ => rfl⟩`.
-/
theorem exists_restr {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (g : GQ l)
    (F : IntermediateField ℚ_[l] (Om l)) (hF : F ≤ Ks K s) :
    ∃ τ : ↥F →ₐ[ℚ_[l]] ↥LL.1, ∀ x : ↥F, (τ x : Om l) = g (x : Om l) :=
  ⟨(g.toAlgHom.comp F.val).codRestrict LL.1.toSubalgebra
    (fun x => h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨x, hF x.2⟩), fun _ => rfl⟩

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp [P.ζQ_zero]`. Consider the case `succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zeta_pow (P : LocPrime l) (m : ℕ) : P.ζQ m ^ l ^ m = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]`.
-/
theorem zeta_pow_one (P : LocPrime l) (m : ℕ) : P.ζQ (m + 1) ^ l ^ m = P.ζQ 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

/- English proof (translation)
Take `⟨m, rfl⟩ : ∃ m, s = m + 1` from `⟨s - 1, by omega⟩`. Establish `hnot : ¬ P.ζQ (m + 1) ^ l ^ m = 1` using `by rw [zeta_pow_one]; exact P.ζQ_one`. Rewrite using `[← orderOf_eq_prime_pow hnot (zeta_pow P (m + 1))]`. Conclude with `IsPrimitiveRoot.orderOf _`.
-/
theorem zeta_prim (P : LocPrime l) (s : ℕ) (hs : 1 ≤ s) : IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hnot : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [zeta_pow_one]; exact P.ζQ_one
  rw [← orderOf_eq_prime_pow hnot (zeta_pow P (m + 1))]
  exact IsPrimitiveRoot.orderOf _

/- English proof (translation)
The claim follows from `(le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zeta_pow P s))`.
-/
theorem zeta_mem (P : LocPrime l) (K : FinExt l) (s : ℕ) : P.ζQ s ∈ Ks K s :=
  (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ (zeta_pow P s))

/- English proof (translation)
The claim follows from `le_sup_left`.
-/
theorem unramifiedSubfield_le_cyclotomicExt (K : FinExt l) (s : ℕ) : K0 K ≤ Ks K s := le_sup_left

/- English proof (translation)
Establish `hb : Function.Bijective (fun f : ↥F →ₐ[ℚ_[l]] ↥LL.1 => LL.1.val.comp f)`. Prove the components needed by the constructor for the conclusion. Introduce `f f' hf`. Conclude with `AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hf x)`. Introduce `f`.

Take `⟨g, hg⟩` from `exists_aut F f`. Take `⟨τ, hτ⟩` from `exists_restr h g F hF`. Conclude with `⟨τ, AlgHom.ext fun x => (hτ x).trans (hg x)⟩`. Rewrite using `[Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card]`. Conclude with `AlgHom.card ℚ_[l] ↥F (Om l)`.
-/
theorem card_emb {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (F : IntermediateField ℚ_[l] (Om l)) [FiniteDimensional ℚ_[l] ↥F] (hF : F ≤ Ks K s) :
    Nat.card (↥F →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥F := by
  have hb : Function.Bijective (fun f : ↥F →ₐ[ℚ_[l]] ↥LL.1 => LL.1.val.comp f) := by
    constructor
    · intro f f' hf
      exact AlgHom.ext fun x => Subtype.ext (DFunLike.congr_fun hf x)
    · intro f
      obtain ⟨g, hg⟩ := exists_aut F f
      obtain ⟨τ, hτ⟩ := exists_restr h g F hF
      exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (hg x)⟩
  rw [Nat.card_eq_of_bijective _ hb, Nat.card_eq_fintype_card]
  exact AlgHom.card ℚ_[l] ↥F (Om l)

variable {P : LocPrime l} (H : LocHW l P) {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)

/- English proof (translation)
Take `⟨τs, hτs⟩` from `exists_restr h g (Ks K s) le_rfl`. Use `⟨τs, ⟨fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩, fun x y hxy => Subtype.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hτs, hxy, h0]`. Rewrite using `[hτs, hy, hζ]`. Rewrite using `[hτs, hxy, hτ]`.
-/
theorem pt_of_aut (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (g : GQ l)
    (h0 : ∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1))
    (hζ : g (P.ζQ s) = ζ) (hτ : ∀ x : ↥K.1, g (x : Om l) = τ x) : Pt H h i ζ τ := by
  obtain ⟨τs, hτs⟩ := exists_restr h g (Ks K s) le_rfl
  refine ⟨τs, ⟨fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩, fun x y hxy => Subtype.ext ?_⟩
  · rw [hτs, hxy, h0]
  · rw [hτs, hy, hζ]
  · rw [hτs, hxy, hτ]

/- English proof (translation)
Take `⟨τs, ⟨h1, h2⟩, h3⟩` from `hp`. Take `⟨g, hg⟩` from `exists_aut (Ks K s) (LL.1.val.comp τs)`. Use `⟨g, fun c => ?_, ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]`. Conclude with `hg ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩`.

Rewrite using `[← h2 ⟨_, zeta_mem P K s⟩ rfl]`. Conclude with `hg ⟨_, zeta_mem P K s⟩`. Rewrite using `[h3 x ⟨x, h.2.2.1 x.2⟩ rfl]`. Conclude with `hg ⟨x, h.2.2.1 x.2⟩`.
-/
theorem aut_of_pt (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    ∃ g : GQ l, (∀ c : ↥(K0 K), g (c : Om l) = ((H.W K s LL h).emb i c : ↥LL.1)) ∧
      g (P.ζQ s) = ζ ∧ ∀ x : ↥K.1, g (x : Om l) = τ x := by
  obtain ⟨τs, ⟨h1, h2⟩, h3⟩ := hp
  obtain ⟨g, hg⟩ := exists_aut (Ks K s) (LL.1.val.comp τs)
  refine ⟨g, fun c => ?_, ?_, fun x => ?_⟩
  · rw [← h1 c ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩ rfl]
    exact hg ⟨c, unramifiedSubfield_le_cyclotomicExt K s c.2⟩
  · rw [← h2 ⟨_, zeta_mem P K s⟩ rfl]
    exact hg ⟨_, zeta_mem P K s⟩
  · rw [h3 x ⟨x, h.2.2.1 x.2⟩ rfl]
    exact hg ⟨x, h.2.2.1 x.2⟩

/- English proof (translation)
Take `⟨g₀, hg₀⟩` from `exists_aut (K0 K) (LL.1.val.comp ((H.W K s LL h).emb i))`. Establish `h1 : IsPrimitiveRoot (g₀.symm (ζ : Om l)) (l ^ s)` using `(hζ.map_of_injective (f := LL.1.val) LL.1.val.toRingHom.injective).map_of_injective g₀.symm.injective`. Establish `hconj : IsConjRoot ↥(K0 K) (g₀.symm (ζ : Om l)) (P.ζQ s)`. Unfold `IsConjRoot`. Rewrite using `[GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ h1, GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ (zeta_prim P s h.1)]`.

Take `⟨σ, hσ⟩` from `hconj.exists_algEquiv`. Take `⟨τ, hτ⟩` from `exists_restr h ((σ.restrictScalars ℚ_[l]).trans g₀) K.1 h.2.2.1`. Use `⟨τ, pt_of_aut H h i ζ τ ((σ.restrictScalars ℚ_[l]).trans g₀) (fun c => ?_) ?_ (fun x => (hτ x).symm)⟩` and prove the remaining obligations. Establish `: σ (c : Om l) = c` using `σ.commutes c`. Express the relevant statement in the definitionally equal form `g₀ (σ (c : Om l)) = _`.

Rewrite using `[this]`. Conclude with `hg₀ c`. Express the relevant statement in the definitionally equal form `g₀ (σ (P.ζQ s)) = _`. Rewrite using `[hσ, AlgEquiv.apply_symm_apply]`.
-/
theorem exists_pt (i : Let K) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) : ∃ τ, Pt H h i ζ τ := by
  obtain ⟨g₀, hg₀⟩ := exists_aut (K0 K) (LL.1.val.comp ((H.W K s LL h).emb i))
  have h1 : IsPrimitiveRoot (g₀.symm (ζ : Om l)) (l ^ s) :=
    (hζ.map_of_injective (f := LL.1.val) LL.1.val.toRingHom.injective).map_of_injective g₀.symm.injective
  have hconj : IsConjRoot ↥(K0 K) (g₀.symm (ζ : Om l)) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ h1,
      GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s h.1 _ (zeta_prim P s h.1)]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  obtain ⟨τ, hτ⟩ := exists_restr h ((σ.restrictScalars ℚ_[l]).trans g₀) K.1 h.2.2.1
  refine ⟨τ, pt_of_aut H h i ζ τ ((σ.restrictScalars ℚ_[l]).trans g₀) (fun c => ?_) ?_
    (fun x => (hτ x).symm)⟩
  · have : σ (c : Om l) = c := σ.commutes c
    change g₀ (σ (c : Om l)) = _
    rw [this]
    exact hg₀ c
  · change g₀ (σ (P.ζQ s)) = _
    rw [hσ, AlgEquiv.apply_symm_apply]

/- English proof (translation)
Take `⟨g, h0, hζ, hτ⟩` from `aut_of_pt H h i ζ τ hp`. Use `⟨?_, ?_, (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp (g.symm.toAlgHom.comp LL.1.val), fun c => ?_, ?_, fun c => ?_⟩` and prove the remaining obligations. Establish `h1` using `(zeta_prim P s h.1).map_of_injective g.injective`. Rewrite `h1` using `[hζ]`. Conclude with `IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) h1 LL.1.val.toRingHom.injective`.

Use `AlgHom.ext fun c => Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[← h0 c]`. Conclude with `(hτ _).symm`. Express the relevant statement in the definitionally equal form `algebraMap (Om l) P.R.BdR (g.symm (((H.W K s LL h).emb i c : ↥LL.1) : Om l)) = _`. Rewrite using `[← h0 c, AlgEquiv.symm_apply_apply]`.

Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `algebraMap (Om l) P.R.BdR (g.symm (ζ : Om l)) = _`. Rewrite using `[← hζ, AlgEquiv.symm_apply_apply]`. Express the relevant statement in the definitionally equal form `algebraMap (Om l) P.R.BdR (g.symm ((τ c : ↥LL.1) : Om l)) = _`. Rewrite using `[← hτ c, AlgEquiv.symm_apply_apply]`.

Both sides reduce to the same expression.
-/
theorem pt_props (i : Let K) (ζ : ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (hp : Pt H h i ζ τ) :
    IsPrimitiveRoot ζ (l ^ s) ∧
      τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = (H.W K s LL h).emb i ∧
      ∃ ι, Comp H h i ζ τ ι := by
  obtain ⟨g, h0, hζ, hτ⟩ := aut_of_pt H h i ζ τ hp
  refine ⟨?_, ?_, (IsScalarTower.toAlgHom ℚ_[l] (Om l) P.R.BdR).comp
    (g.symm.toAlgHom.comp LL.1.val), fun c => ?_, ?_, fun c => ?_⟩
  · have h1 := (zeta_prim P s h.1).map_of_injective g.injective
    rw [hζ] at h1
    exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) h1 LL.1.val.toRingHom.injective
  · refine AlgHom.ext fun c => Subtype.ext ?_
    rw [← h0 c]
    exact (hτ _).symm
  · change algebraMap (Om l) P.R.BdR (g.symm (((H.W K s LL h).emb i c : ↥LL.1) : Om l)) = _
    rw [← h0 c, AlgEquiv.symm_apply_apply]
    rfl
  · change algebraMap (Om l) P.R.BdR (g.symm (ζ : Om l)) = _
    rw [← hζ, AlgEquiv.symm_apply_apply]
  · change algebraMap (Om l) P.R.BdR (g.symm ((τ c : ↥LL.1) : Om l)) = _
    rw [← hτ c, AlgEquiv.symm_apply_apply]
    rfl

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_aut K.1 (LL.1.val.comp τ)`. Take `⟨i, hi⟩` from `(H.W K s LL h).emb_bij.2 (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))`. Use `⟨i, ⟨g (P.ζQ s), h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨_, zeta_mem P K s⟩⟩, pt_of_aut H h i _ τ g (fun c => ?_) rfl hg⟩` and prove the remaining obligations. Rewrite using `[hi]`. Conclude with `hg (algebraMap ↥(K0 K) ↥K.1 c)`.
-/
theorem exists_pt_over (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) : ∃ (i : Let K) (ζ : ↥LL.1), Pt H h i ζ τ := by
  obtain ⟨g, hg⟩ := exists_aut K.1 (LL.1.val.comp τ)
  obtain ⟨i, hi⟩ := (H.W K s LL h).emb_bij.2 (τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1))
  refine ⟨i, ⟨g (P.ζQ s), h.2.2.2 (g.toAlgHom.comp (Ks K s).val) ⟨_, zeta_mem P K s⟩⟩,
    pt_of_aut H h i _ τ g (fun c => ?_) rfl hg⟩
  rw [hi]
  exact hg (algebraMap ↥(K0 K) ↥K.1 c)

/- English proof (translation)
Introduce `D HW l _ K s LL h`. Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2`. Use `haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap (IntermediateField.inclusion_injective inf_le_left)`. Conclude with `⟨exists_pt (HW l) h, pt_props (HW l) h, exists_pt_over (HW l) h, card_emb h K.1 h.2.2.1, card_emb h (K0 K) (unramifiedSubfield_le_cyclotomicExt K s)⟩`.
-/
theorem points : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; (∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ τ, Pt (HW l) h i ζ τ) ∧ (∀ (i : Let K) (ζ : ↥LL.1) τ, Pt (HW l) h i ζ τ → IsPrimitiveRoot ζ (l ^ s) ∧ τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb i ∧ ∃ ι, Comp (HW l) h i ζ τ ι) ∧ (∀ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ (i : Let K) (ζ : ↥LL.1), Pt (HW l) h i ζ τ) ∧ Nat.card (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥K.1 ∧ Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = Module.finrank ℚ_[l] ↥(K0 K) := by
  intro D HW l _ K s LL h
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  exact ⟨exists_pt (HW l) h, pt_props (HW l) h, exists_pt_over (HW l) h,
    card_emb h K.1 h.2.2.1, card_emb h (K0 K) (unramifiedSubfield_le_cyclotomicExt K s)⟩

end GlobalTheory.NL.Points
