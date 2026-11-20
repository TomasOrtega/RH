import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftSurj
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.IdemDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftOfS
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.LiftConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.TrRep
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.Kill0
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private def conjHom {O : Type} [CommRing O] {n : ℕ} (Q : GL (Fin n) O) :
    Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) O where
  toFun Z := ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * Z * (Q : Matrix (Fin n) (Fin n) O)
  map_one' := by rw [Matrix.mul_one, Units.inv_mul]
  map_mul' a b := by
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Introduce `n O R X G _ _ _ _ _ _ _ _ _ D χ x δ ρ c₀ hn hχ hres hx hc hspan hδ`. Take `⟨E, _, _, π, τ, e, hπ, hτ, hg⟩` from `UpperTheory.V.Th.Coc.gma (O := O) D χ hn hχ hres`. Take `⟨htr, hsm, -⟩` from `UpperTheory.V.Th.Coc.trRep D x ρ hn hx`. Take `⟨k1, -⟩` from `UpperTheory.V.Th.Coc.kill0 ρ c₀ hc hspan`. Establish `hs : ∀ g, repR x ρ (MonoidAlgebra.single g (1 : R)) = ρ g` using `fun g => by`.

Rewrite using `[repR_single, map_one, one_smul]`. Establish `hker : RingHom.ker π.toRingHom ≤ RingHom.ker (repR x ρ)`. Introduce `y hy`. Establish `hy' : π y = 0` using `hy`. Use `k1 _ fun g => ?_` and prove the remaining obligations.

Establish `h` using `htr (MonoidAlgebra.single g 1 * y)`. Rewrite `h` using `[map_mul, hs, ← hτ, map_mul, hy', mul_zero, map_zero, map_zero]`. Conclude with `h`. Take `⟨ρE, hρE⟩ : ∃ ρE : E →+* Matrix (Fin n) (Fin n) O, ∀ y, ρE (π y) = repR x ρ y` from `⟨π.toRingHom.liftOfSurjective hπ ⟨repR x ρ, hker⟩, fun y => π.toRingHom.liftOfRightInverse_comp_apply _ _ ⟨repR x ρ, hker⟩ y⟩`. Establish `htrE : ∀ a, (ρE a).trace = x (τ a)` using `fun a => by`.

Take `⟨y, rfl⟩` from `hπ a`. Rewrite using `[hρE, htr, hτ]`. Establish `hsmE : ∀ (r : R) a, ρE (r • a) = x r • ρE a` using `fun r a => by`. Take `⟨y, rfl⟩` from `hπ a`. Rewrite using `[← map_smul π, hρE, hρE, hsm]`.

Establish `hrange : ∀ Z ∈ Submodule.span O (Set.range ρ), ∃ a, ρE a = Z`. Introduce `Z hZ`. Proceed by induction on `hZ using Submodule.span_induction with`. Consider the case `mem Z hZ`. Take `⟨g, rfl⟩` from `hZ`.

Conclude with `⟨π (MonoidAlgebra.single g 1), by rw [hρE, hs]⟩`. Consider the case `zero => exact ⟨0, map_zero _⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨a', rfl⟩` from `ha`. Take `⟨b', rfl⟩` from `hb`.

Conclude with `⟨a' + b', map_add _ _ _⟩`. Consider the case `smul o a _ ha`. Take `⟨a', rfl⟩` from `ha`. Conclude with `⟨algebraMap O R o • a', by rw [hsmE, AlgHom.commutes]; rfl⟩`. Take `⟨Q, hQ⟩` from `UpperTheory.V.Th.Coc.idemDiag (fun i => ρE (e i)) (hg.idem.map ρE) (fun i => by rw [htrE, hg.one, map_one])`.

Set `ρ' : E →+* Matrix (Fin n) (Fin n) O` to `(conjHom Q).comp ρE`. Establish `hρ' : ∀ a, ρ' a = ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ρE a * (Q : Matrix (Fin n) (Fin n) O)` using `fun a => rfl`. Establish `htr' : ∀ a, (ρ' a).trace = x (τ a)` using `fun a => by`. Rewrite using `[hρ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, htrE]`. Establish `hsm' : ∀ (r : R) a, ρ' (r • a) = x r • ρ' a` using `fun r a => by`.

Rewrite using `[hρ', hρ', hsmE, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hsurj' : ∀ Z, ∃ a, ρ' a = c₀ • Z` using `fun Z => by`. Take `⟨a, ha⟩` from `hrange _ (hspan ((Q : Matrix (Fin n) (Fin n) O) * Z * ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ', ha, Matrix.mul_smul, Matrix.smul_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]`. Take `⟨s, β, hβ, h1, h2, h3⟩` from `UpperTheory.V.Th.Coc.smat x ρ' τ e c₀ hn hg hQ htr' hsurj'`. Take `⟨d, hd⟩` from `UpperTheory.V.Th.Coc.liftOfS x δ ρ' τ s β (c₀ ^ (2 * n)) hδ hsm' htr' hβ h1 h2 h3`. Take `⟨d', hd', -⟩` from `UpperTheory.V.Th.Coc.liftConj x δ ρE ρ' τ _ Q d (fun a => by`.

Rewrite using `[hρ']`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]) hd`. Use `⟨d'.comp π.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a b`.

Establish `h` using `hd'.mul (π a) (π b)`. Rewrite `h` using `[← map_mul, hρE, hρE]`. Conclude with `h`. Introduce `r a`. Establish `h` using `hd'.smul r (π a)`.

Rewrite `h` using `[← map_smul π, hρE]`. Conclude with `h`. Introduce `a`. Establish `h` using `hd'.tr (π a)`. Rewrite `h` using `[hτ]`.

Conclude with `h`.
-/
theorem UpperTheory.V.Th.Coc.liftG :
    ∀ {n : ℕ} {O R X G : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing X] [Algebra O X] [Group G] (D : GDet n R G) (χ : Fin n → G →* (ResidueField O)ˣ) (x : R →ₐ[O] O) (δ : R →ₗ[O] X) (ρ : G →* Matrix (Fin n) (Fin n) O) (c₀ : O), 1 ≤ n → Function.Injective χ → D.map (res O R : R →+* ResidueField O) = GDet.ofRep (diagRep χ) → D.map x.toRingHom = GDet.ofRep ρ → c₀ ≠ 0 → (∀ Z : Matrix (Fin n) (Fin n) O, c₀ • Z ∈ Submodule.span O (Set.range ρ)) → IsDer x δ → ∃ d : MonoidAlgebra R G →+ Matrix (Fin n) (Fin n) X, IsLift x δ (repR x ρ) D.tr (c₀ ^ (2 * n) * c₀ ^ (2 * n)) d := by
  intro n O R X G _ _ _ _ _ _ _ _ _ D χ x δ ρ c₀ hn hχ hres hx hc hspan hδ
  obtain ⟨E, _, _, π, τ, e, hπ, hτ, hg⟩ := UpperTheory.V.Th.Coc.gma (O := O) D χ hn hχ hres
  obtain ⟨htr, hsm, -⟩ := UpperTheory.V.Th.Coc.trRep D x ρ hn hx
  obtain ⟨k1, -⟩ := UpperTheory.V.Th.Coc.kill0 ρ c₀ hc hspan
  have hs : ∀ g, repR x ρ (MonoidAlgebra.single g (1 : R)) = ρ g := fun g => by
    rw [repR_single, map_one, one_smul]
  have hker : RingHom.ker π.toRingHom ≤ RingHom.ker (repR x ρ) := by
    intro y hy
    have hy' : π y = 0 := hy
    refine k1 _ fun g => ?_
    have h := htr (MonoidAlgebra.single g 1 * y)
    rw [map_mul, hs, ← hτ, map_mul, hy', mul_zero, map_zero, map_zero] at h
    exact h
  obtain ⟨ρE, hρE⟩ : ∃ ρE : E →+* Matrix (Fin n) (Fin n) O, ∀ y, ρE (π y) = repR x ρ y :=
    ⟨π.toRingHom.liftOfSurjective hπ ⟨repR x ρ, hker⟩, fun y =>
      π.toRingHom.liftOfRightInverse_comp_apply _ _ ⟨repR x ρ, hker⟩ y⟩
  have htrE : ∀ a, (ρE a).trace = x (τ a) := fun a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [hρE, htr, hτ]
  have hsmE : ∀ (r : R) a, ρE (r • a) = x r • ρE a := fun r a => by
    obtain ⟨y, rfl⟩ := hπ a
    rw [← map_smul π, hρE, hρE, hsm]
  have hrange : ∀ Z ∈ Submodule.span O (Set.range ρ), ∃ a, ρE a = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      exact ⟨π (MonoidAlgebra.single g 1), by rw [hρE, hs]⟩
    | zero => exact ⟨0, map_zero _⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', map_add _ _ _⟩
    | smul o a _ ha =>
      obtain ⟨a', rfl⟩ := ha
      exact ⟨algebraMap O R o • a', by rw [hsmE, AlgHom.commutes]; rfl⟩
  obtain ⟨Q, hQ⟩ := UpperTheory.V.Th.Coc.idemDiag (fun i => ρE (e i)) (hg.idem.map ρE)
    (fun i => by rw [htrE, hg.one, map_one])
  let ρ' : E →+* Matrix (Fin n) (Fin n) O := (conjHom Q).comp ρE
  have hρ' : ∀ a, ρ' a = ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * ρE a * (Q : Matrix (Fin n) (Fin n) O) :=
    fun a => rfl
  have htr' : ∀ a, (ρ' a).trace = x (τ a) := fun a => by
    rw [hρ', Matrix.trace_mul_comm, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, htrE]
  have hsm' : ∀ (r : R) a, ρ' (r • a) = x r • ρ' a := fun r a => by
    rw [hρ', hρ', hsmE, Matrix.mul_smul, Matrix.smul_mul]
  have hsurj' : ∀ Z, ∃ a, ρ' a = c₀ • Z := fun Z => by
    obtain ⟨a, ha⟩ := hrange _ (hspan ((Q : Matrix (Fin n) (Fin n) O) * Z *
      ((Q⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)))
    refine ⟨a, ?_⟩
    rw [hρ', ha, Matrix.mul_smul, Matrix.smul_mul]
    simp only [Matrix.mul_assoc]
    rw [Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one]
  obtain ⟨s, β, hβ, h1, h2, h3⟩ := UpperTheory.V.Th.Coc.smat x ρ' τ e c₀ hn hg hQ htr' hsurj'
  obtain ⟨d, hd⟩ := UpperTheory.V.Th.Coc.liftOfS x δ ρ' τ s β (c₀ ^ (2 * n)) hδ hsm' htr' hβ h1 h2 h3
  obtain ⟨d', hd', -⟩ := UpperTheory.V.Th.Coc.liftConj x δ ρE ρ' τ _ Q d (fun a => by
    rw [hρ']
    simp only [Matrix.mul_assoc]
    rw [Units.mul_inv_cancel_left, Units.mul_inv, Matrix.mul_one]) hd
  refine ⟨d'.comp π.toRingHom.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro a b
    have h := hd'.mul (π a) (π b)
    rw [← map_mul, hρE, hρE] at h
    exact h
  · intro r a
    have h := hd'.smul r (π a)
    rw [← map_smul π, hρE] at h
    exact h
  · intro a
    have h := hd'.tr (π a)
    rw [hτ] at h
    exact h
