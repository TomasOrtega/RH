import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair)
open GlobalTheory.FinPl

namespace GlobalTheory.FinPl

section Mix

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, hee, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, hee, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]`.
-/
theorem mix_mul_decompAt (e : A) (hee : e * e = e) (a b : Matrix n n A) :
    (e • a + (1 - e) • (1 : Matrix n n A)) * (e • b + (1 - e) • 1) = e • (a * b) + (1 - e) • 1 := by
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
  simp only [add_mul, mul_add, smul_mul_smul_comm, hee, h1, h2, h3, zero_smul, add_zero, zero_add, mul_one, one_mul]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply, map_add, map_mul, map_sub, map_one, hs]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[hij, Ne.symm hij]`.
-/
theorem cT_mix_decompAt (s : A →+* A) (e : A) (hs : s e = e) (a : Matrix n n A) :
    Formalism.UG.cT s (e • a + (1 - e) • (1 : Matrix n n A)) = e • Formalism.UG.cT s a + (1 - e) • 1 := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, map_add, map_mul, map_sub, map_one, hs]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Ne.symm hij]

/- English proof (translation)
Use `⟨⟨e • (g : Matrix n n A) + (1 - e) • 1, e • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[mix_mul_decompAt e hee, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul]`. Rewrite using `[mix_mul_decompAt e hee, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]`. Establish `hg' : Formalism.UG.cT s (g : Matrix n n A) ⬝ J ⬝ (g : Matrix n n A) = J` using `hg show Formalism.UG.cT s (e • (g : Matrix n n A) + (1 - e) • 1) ⬝ J ⬝ (e • (g : Matrix n n A) + (1 - e) • 1) = J`. Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, hee, sub_self]`.

Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Establish `h3 : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, one_mul, h1, sub_zero]`. Rewrite using `[cT_mix_decompAt s e hs]`. Simplify using `only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one] at hg' ⊢`. Rewrite using `[hg', hee, h1, h2, h3, zero_smul, zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]`.
-/
theorem mix_mem_decompAt (s : A →+* A) (J : Matrix n n A) (e : A) (hee : e * e = e) (hs : s e = e) (g : GL n A)
    (hg : g ∈ Formalism.UG.UJ s J) :
    ∃ g' ∈ Formalism.UG.UJ s J, (g' : Matrix n n A) = e • (g : Matrix n n A) + (1 - e) • 1 := by
  refine ⟨⟨e • (g : Matrix n n A) + (1 - e) • 1, e • ((g⁻¹ : GL n A) : Matrix n n A) + (1 - e) • 1, ?_, ?_⟩, ?_, rfl⟩
  · rw [mix_mul_decompAt e hee, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul]
  · rw [mix_mul_decompAt e hee, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]
  · have hg' : Formalism.UG.cT s (g : Matrix n n A) ⬝ J ⬝ (g : Matrix n n A) = J := hg
    show Formalism.UG.cT s (e • (g : Matrix n n A) + (1 - e) • 1) ⬝ J ⬝ (e • (g : Matrix n n A) + (1 - e) • 1) = J
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, h1, sub_zero]
    rw [cT_mix_decompAt s e hs]
    simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, one_mul, mul_one] at hg' ⊢
    rw [hg', hee, h1, h2, h3, zero_smul, zero_smul, add_zero, zero_add, ← add_smul, add_sub_cancel, one_smul]

/- English proof (translation)
Use extensionality with `i j`. Establish `key : (1 : Matrix n n (A ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix n n A) i j)`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Simplify using `only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]`. Rewrite using `[key]`.

Conclude with `Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using hg i j)`.
-/
theorem map_mk_decompAt (I : Ideal A) (g : GL n A) (hg : ∀ i j, ((g : Matrix n n A) - 1) i j ∈ I) :
    Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g = 1 := by
  ext i j
  have key : (1 : Matrix n n (A ⧸ I)) i j = Ideal.Quotient.mk I ((1 : Matrix n n A) i j) := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one]
  rw [key]
  exact Ideal.Quotient.eq.mpr (by simpa [Matrix.sub_apply] using hg i j)

end Mix

/- English proof (translation)
Simplify using `[sigR, Algebra.TensorProduct.algebraMap_apply]`.
-/
theorem sigR_algebraMap_decompAt {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D S h v`. Take `⟨ε, α, hε, hv1, hv0⟩` from `GlobalTheory.IdemSupport.exists_placeIdem (D := D) v`. Take `⟨h0, hc⟩` from `placeIdempotent_infinite_and_finite_components D v ε α hε`. Establish `hea : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E)`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]`.

Use `set e : AE D := algebraMap (AF D.host.F) (AE D) ε with he_def`. Establish `c1 : compAt D v e = 1` using `by rw [hc, hv1]; rfl`. Establish `c0 : ∀ w, w ≠ v → compAt D w e = 0` using `fun w hw => by rw [hc, hv0 w hw, TensorProduct.zero_tmul]`. Establish `heAt : e ∈ idAt D (· = v)` using `(mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ e).2 ⟨h0, fun w hw => c0 w hw⟩`. Establish `hee : e * e = e` using `(mem_supportedAtPlace_iff_placeIdempotent_mul D v e h0 c1 c0 e).1 heAt`.

Establish `heOff : 1 - e ∈ idOff D (· = v)`. Use `(Submodule.mem_iInf _).2 fun w => ?_` and prove the remaining obligations. Break down `w with ⟨w, hw⟩` into its components or cases. Express the relevant statement in the definitionally equal form `w = v at hw`. Substitute `hw` using the available equality.

Rewrite using `[RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, c1, sub_self]`. Establish `hee' : (1 - e) * (1 - e) = 1 - e` using `by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]`. Establish `hσ : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' e = e`. Introduce `σ'`. Conclude with `sigR_algebraMap_decompAt (AF D.host.F) σ' ε`.

Establish `hσ' : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' (1 - e) = 1 - e`. Introduce `σ'`. Rewrite using `[map_sub, map_one, hσ]`. Establish `hmem : h.1 ∈ Formalism.UG.UJ (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram)` using `h.2`. Take `⟨g₁, hg₁, hg₁v⟩` from `mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) e hee (hσ _) h.1 hmem`.

Take `⟨g₂, hg₂, hg₂v⟩` from `mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) (1 - e) hee' (hσ' _) h.1 hmem`. Establish `hcong : ∀ (I : Ideal (AE D)) (g : GA D S), (∀ i j, (mt S g - 1) i j ∈ I) → g ∈ congGrp S I`. Introduce `I g hg`. Rewrite using `[congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]`. Conclude with `map_mk_decompAt I _ hg`.

Establish `h1 : e * (1 - e) = 0` using `by rw [mul_sub, mul_one, hee, sub_self]`. Establish `h2 : (1 - e) * e = 0` using `by rw [mul_comm, h1]`. Use `⟨⟨g₁, hg₁⟩, hcong _ _ ?_, ⟨g₂, hg₂⟩, hcong _ _ ?_, ?_⟩` and prove the remaining obligations. Introduce `i j show (g₁.val - 1) i j ∈ _`. Establish `: e • h.1.val + (1 - e) • 1 - 1 = e • (h.1.val - 1)`.

Rewrite using `[smul_sub, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hg₁v, this, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ heAt`. Introduce `i j show (g₂.val - 1) i j ∈ _`.

Establish `: (1 - e) • h.1.val + (1 - (1 - e)) • 1 - 1 = (1 - e) • (h.1.val - 1)`. Rewrite using `[smul_sub, sub_smul (1 : AE D) (1 - e), one_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[hg₂v, this, Matrix.smul_apply, smul_eq_mul]`. Conclude with `Ideal.mul_mem_right _ _ heOff`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use `show h.1.val = g₁.val * g₂.val`. Rewrite using `[hg₁v, hg₂v, sub_sub_cancel]`. Simplify using `only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hee, hee', h1, h2, zero_smul, zero_add, add_zero]`.

Rewrite using `[add_comm, ← add_smul, add_sub_cancel, one_smul]`.
-/
theorem decompAt : ∀ (D : D7) (S : HSp D) (h : GA D S) (v : Pl D), ∃ hv ∈ grpAt S (· = v), ∃ h' ∈ grpOff S (· = v),
    h = hv * h' := by
  intro D S h v
  obtain ⟨ε, α, hε, hv1, hv0⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hε
  have hea : algebraMap (AF D.host.F) (AE D) ε = ε ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  set e : AE D := algebraMap (AF D.host.F) (AE D) ε with he_def
  have c1 : compAt D v e = 1 := by rw [hc, hv1]; rfl
  have c0 : ∀ w, w ≠ v → compAt D w e = 0 := fun w hw => by rw [hc, hv0 w hw, TensorProduct.zero_tmul]
  have heAt : e ∈ idAt D (· = v) := (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ e).2 ⟨h0, fun w hw => c0 w hw⟩
  have hee : e * e = e := (mem_supportedAtPlace_iff_placeIdempotent_mul D v e h0 c1 c0 e).1 heAt
  have heOff : 1 - e ∈ idOff D (· = v) := by
    refine (Submodule.mem_iInf _).2 fun w => ?_
    rcases w with ⟨w, hw⟩
    change w = v at hw
    subst hw
    rw [RingHom.mem_ker, RingHom.map_sub, RingHom.map_one, c1, sub_self]
  have hee' : (1 - e) * (1 - e) = 1 - e := by rw [sub_mul, one_mul, mul_sub, mul_one, hee, sub_self, sub_zero]
  have hσ : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' e = e := by
    intro σ'
    exact sigR_algebraMap_decompAt (AF D.host.F) σ' ε
  have hσ' : ∀ σ' : D.host.E →ₐ[D.host.F] D.host.E, sigR (AF D.host.F) σ' (1 - e) = 1 - e := by
    intro σ'; rw [map_sub, map_one, hσ]
  have hmem : h.1 ∈ Formalism.UG.UJ (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) := h.2
  obtain ⟨g₁, hg₁, hg₁v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) e hee
    (hσ _) h.1 hmem
  obtain ⟨g₂, hg₂, hg₂v⟩ := mix_mem_decompAt (sigR (AF D.host.F) _) (JR (AF D.host.F) S.gram) (1 - e)
    hee' (hσ' _) h.1 hmem
  have hcong : ∀ (I : Ideal (AE D)) (g : GA D S), (∀ i j, (mt S g - 1) i j ∈ I) → g ∈ congGrp S I := by
    intro I g hg
    rw [congGrp, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_mk_decompAt I _ hg
  have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
  refine ⟨⟨g₁, hg₁⟩, hcong _ _ ?_, ⟨g₂, hg₂⟩, hcong _ _ ?_, ?_⟩
  · intro i j
    show (g₁.val - 1) i j ∈ _
    have : e • h.1.val + (1 - e) • 1 - 1 = e • (h.1.val - 1) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hg₁v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heAt
  · intro i j
    show (g₂.val - 1) i j ∈ _
    have : (1 - e) • h.1.val + (1 - (1 - e)) • 1 - 1 =
        (1 - e) • (h.1.val - 1) := by
      rw [smul_sub, sub_smul (1 : AE D) (1 - e), one_smul]; abel
    rw [hg₂v, this, Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ heOff
  · apply Subtype.ext
    apply Units.ext
    show h.1.val = g₁.val * g₂.val
    rw [hg₁v, hg₂v, sub_sub_cancel]
    simp only [add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, hee, hee', h1, h2, zero_smul, zero_add,
      add_zero]
    rw [add_comm, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.FinPl
