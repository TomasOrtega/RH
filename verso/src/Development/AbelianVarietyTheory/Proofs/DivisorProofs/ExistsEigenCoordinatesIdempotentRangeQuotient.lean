import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIdempotentsOfComaximalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientRetractPiQuotientOfSummandStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordsRangeIdempotentOfRetractStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

/- English proof (translation)
Introduce `C _ _ I hI2 A _ H _ _ _ _ σ a χ hχ π hπ hσπ F hIF hσF hπF hEM hdec`. Establish `hItop : I ≠ ⊤`. Introduce and unpack `rfl`. Rewrite `hI2` using `[Ideal.top_pow]`. Conclude with `top_ne_bot hI2`.

Take `⟨m, s, r, hrs⟩` from `GlobalTheory.T.quotient_retract_pi_quotient_of_summand I F hIF hEM`. Set `σb : A →+* Module.End C (H ⧸ F)` to `{ toFun := fun c => F.mapQ F (σ c) (fun x hx => hσF c x hx) map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp) map_mul' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp) map_zero' := Submodule.linearMap_qext _ (LinearMap.ext fun x => b …`. Establish `hσb : ∀ c x, σb c (F.mkQ x) = F.mkQ (σ c x)` using `fun c x => rfl`. Set `πb : Module.End C (H ⧸ F)` to `F.mapQ F π (fun x hx => hπF x hx)`. Establish `hπb : ∀ x, πb (F.mkQ x) = F.mkQ (π x)` using `fun x => rfl`.

Establish `hπσ : ∀ c, πb * σb c = σb c * πb` using `fun c => Submodule.linearMap_qext _ (LinearMap.ext fun x => by`. Simplify using `only [LinearMap.comp_apply, Module.End.mul_apply, hσb, hπb]`. Rewrite using `[← Module.End.mul_apply, ← hσπ c, Module.End.mul_apply])`. Establish `hσσ : ∀ c d, σb c * σb d = σb d * σb c` using `fun c d => by`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`.

Take `⟨e, he1, he2, he3⟩` from `GlobalTheory.T.exists_eigen_idempotents_of_comaximal σb a χ hχ`. Establish `heπ : ∀ i, πb * e i = e i * πb` using `fun i => he1 i πb hπσ`. Establish `heσ : ∀ i c, σb c * e i = e i * σb c` using `fun i c => he1 i (σb c) (hσσ c)`. Establish `hππ : πb * πb = πb` using `Submodule.linearMap_qext _ (LinearMap.ext fun x => by`. Simplify using `only [LinearMap.comp_apply, Module.End.mul_apply, hπb]`.

Rewrite using `[← Module.End.mul_apply, hπ])`. Establish `hD : ∀ x ∈ LinearMap.range π, ∃ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) ∧ F.mkQ x = ∑ i, u i`. Introduce `x hx`. Take `⟨w, hw1, hw2⟩` from `hdec x hx`. Use `⟨fun i => F.mkQ (w i), fun i c => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hσb, ← map_smul, ← sub_eq_zero, ← map_sub]`. Conclude with `(Submodule.Quotient.mk_eq_zero F).2 (hw1 i c)`. Rewrite using `[← map_sum, ← sub_eq_zero, ← map_sub]`. Conclude with `(Submodule.Quotient.mk_eq_zero F).2 hw2`. Establish `hEu : ∀ x ∈ LinearMap.range π, ∀ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) → F.mkQ x = ∑ i, u i → ∀ i, e i (F.mkQ x) = u i`.

Introduce `x hx u hu hxu i`. Rewrite using `[hxu, map_sum, Finset.sum_eq_single i]`. Conclude with `he2 i (u i) (hu i)`. Introduce `j _ hji`. Conclude with `he3 i j (u j) hji (hu j)`.

Simplify using the standard rewrite rules. Set `p : Fin a → Module.End C (H ⧸ F)` to `fun i => e i * πb`. Establish `hpx : ∀ i x, p i (F.mkQ x) = e i (F.mkQ (π x))` using `fun i x => rfl`. Establish `hpσ : ∀ i c, p i * σb c = σb c * p i` using `fun i c => by`. Simplify using `only [p]`.

Rewrite using `[_root_.mul_assoc, hπσ, ← _root_.mul_assoc, ← heσ, _root_.mul_assoc]`. Establish `hpE : ∀ i w, ∀ c, σb c (p i w) = χ i c • p i w`. Introduce `i w c`. Take `⟨x, rfl⟩` from `Submodule.mkQ_surjective F w`. Take `⟨u, hu, hxu⟩` from `hD (π x) (LinearMap.mem_range_self π x)`.

Rewrite using `[hpx, hEu _ (LinearMap.mem_range_self π x) u hu hxu]`. Conclude with `hu i c`. Establish `hpe : ∀ i w, (∀ c, σb c w = χ i c • w) → e i (p i w) = p i w` using `fun i w _ => he2 i _ (hpE i w)`. Establish `hpπ : ∀ i w, πb (p i w) = p i w`. Introduce `i w`.

Simplify using `only [p]`. Rewrite using `[← Module.End.mul_apply, ← _root_.mul_assoc, heπ, _root_.mul_assoc, hππ]`. Establish `hpp : ∀ i j w, p j (p i w) = if j = i then p i w else 0`. Introduce `i j w`. Use `show e j (πb (p i w)) = _`.

Rewrite using `[hpπ]`. Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `he2 j _ (hpE j w)`. Conclude with `he3 j i _ (Ne.symm h) (hpE i w)`.

Establish `hidem : ∀ i, p i * p i = p i` using `fun i => LinearMap.ext fun w => by`. Rewrite using `[Module.End.mul_apply, hpp]`. Simplify using the standard rewrite rules. Use `choose n b f hb hfp hδ hinj using fun i => GlobalTheory.T.exists_coords_range_idempotent_of_retract I hItop m s r hrs (p i) (hidem i)`. Take `⟨eqv⟩ : Nonempty ((Σ i, Fin (n i)) ≃ Fin (∑ i, n i))` from `⟨finSigmaFinEquiv⟩`.

Establish `hlift : ∀ i t, ∃ z ∈ LinearMap.range π, F.mkQ z = b i t`. Introduce `i t`. Take `⟨w, hw⟩` from `hb i t`. Take `⟨h', hh'⟩` from `Submodule.mkQ_surjective F (e i w)`. Use `⟨π h', LinearMap.mem_range_self π h', ?_⟩` and prove the remaining obligations.

Rewrite using `[← hw, ← hπb, hh']`. Use `show πb (e i w) = (e i * πb) w`. Rewrite using `[← Module.End.mul_apply, heπ]`. Use `choose z hz hzb using hlift`. Set `L : (Σ i, Fin (n i)) → H →ₗ[C] C ⧸ I` to `fun q => f q.1 q.2 ∘ₗ F.mkQ`.

Set `Z : (Σ i, Fin (n i)) → H` to `fun q => z q.1 q.2`. Establish `hL : ∀ i t x, L ⟨i, t⟩ x = f i t (F.mkQ x)` using `fun _ _ _ => rfl`. Establish `hZ : ∀ i t, Z ⟨i, t⟩ = z i t` using `fun _ _ => rfl`. Use `⟨∑ i, n i, fun k => (eqv.symm k).1, fun k => L (eqv.symm k), fun k => Z (eqv.symm k), ?_, ?_, fun k => hz _ _, ?_⟩` and prove the remaining obligations. Introduce `k c x`.

Take `⟨⟨i, t⟩, rfl⟩` from `eqv.surjective k`. Simplify using `only [Equiv.symm_apply_apply, hL]`. Rewrite using `[← hσb, ← hfp i t, ← Module.End.mul_apply, hpσ, Module.End.mul_apply, hpE, map_smul, hfp, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]`. Introduce `x hx`. Prove the components needed by the constructor for the conclusion.

Introduce `hxF k`. Establish `h0 : F.mkQ x = 0` using `(Submodule.Quotient.mk_eq_zero F).2 hxF`. Simplify using `only [L, LinearMap.comp_apply, h0, map_zero]`. Introduce `hk`. Take `⟨u, hu, hxu⟩` from `hD x hx`.

Establish `hpu : ∀ i, p i (F.mkQ x) = u i`. Introduce `i`. Take `⟨x', rfl⟩` from `hx`. Establish `hx' : π (π x') = π x'` using `by rw [← Module.End.mul_apply, hπ]`. Rewrite using `[hpx, hx']`.

Conclude with `hEu _ (LinearMap.mem_range_self π x') u hu hxu i`. Establish `h0 : ∀ i, u i = 0`. Introduce `i`. Rewrite using `[← hpu i]`. Use `hinj i _ (LinearMap.mem_range_self _ _) fun t => ?_` and prove the remaining obligations.

Rewrite using `[hfp]`. Simplify `hk (eqv ⟨i, t⟩)` using `[hL]`. Rewrite using `[← Submodule.Quotient.mk_eq_zero F]`. Express the relevant statement in the definitionally equal form `F.mkQ x = 0`. Rewrite using `[hxu]`.

Simplify using `[h0]`. Introduce `j k`. Take `⟨⟨i', t'⟩, rfl⟩` from `eqv.surjective j`. Take `⟨⟨i, t⟩, rfl⟩` from `eqv.surjective k`. Simplify using `only [Equiv.symm_apply_apply, hL, hZ, hzb, eqv.injective.eq_iff]`.

Distinguish the cases in `hii : i' = i`. Substitute `hii` using the available equality. Rewrite using `[hδ]`. Simplify using the standard rewrite rules. Establish `: f i' t' (b i t) = 0`.

Take `⟨w, hw⟩` from `hb i t`. Rewrite using `[← hfp, ← hw, hpp, if_neg hii, map_zero]`. Rewrite using `[this, if_neg]`. Introduce `h`. Conclude with `hii (congrArg Sigma.fst h)`.
-/
theorem exists_eigen_coordinates_range_quot : ∀ {C : Type} [CommRing C] [IsLocalRing C] (I : Ideal C), I ^ 2 = ⊥ →
  ∀ {A : Type} [CommRing A] {H : Type u} [AddCommGroup H] [Module C H] [Module.Finite C H] [Module.Projective C H]
  (σ : A →+* Module.End C H) (a : ℕ) (χ : Fin a → A →+* C),
  (∀ i j, i ≠ j → Ideal.span (Set.range fun x => χ i x - χ j x) = ⊤) →
  ∀ (π : Module.End C H), π * π = π → (∀ c, σ c * π = π * σ c) →
  ∀ (F : Submodule C H), I • ⊤ ≤ F → (∀ c, ∀ x ∈ F, σ c x ∈ F) → (∀ x ∈ F, π x ∈ F) →
  (∃ E' M : Submodule C H, IsCompl E' M ∧ E' ⊔ I • ⊤ = F) →
  (∀ d ∈ LinearMap.range π, ∃ w : Fin a → H, (∀ i c, σ c (w i) - χ i c • w i ∈ F) ∧ d - ∑ i, w i ∈ F) →
  ∃ (n : ℕ) (κ : Fin n → Fin a) (ℓ : Fin n → H →ₗ[C] C ⧸ I) (y : Fin n → H),
    (∀ k c x, ℓ k (σ c x) = Ideal.Quotient.mk I (χ (κ k) c) * ℓ k x) ∧
    (∀ x ∈ LinearMap.range π, x ∈ F ↔ ∀ k, ℓ k x = 0) ∧
    (∀ k, y k ∈ LinearMap.range π) ∧ ∀ j k, ℓ j (y k) = if j = k then 1 else 0 := by
  intro C _ _ I hI2 A _ H _ _ _ _ σ a χ hχ π hπ hσπ F hIF hσF hπF hEM hdec
  have hItop : I ≠ ⊤ := by
    rintro rfl
    rw [Ideal.top_pow] at hI2
    exact top_ne_bot hI2
  obtain ⟨m, s, r, hrs⟩ := GlobalTheory.T.quotient_retract_pi_quotient_of_summand I F hIF hEM
  let σb : A →+* Module.End C (H ⧸ F) :=
    { toFun := fun c => F.mapQ F (σ c) (fun x hx => hσF c x hx)
      map_one' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_mul' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_zero' := Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp)
      map_add' := fun c d => Submodule.linearMap_qext _ (LinearMap.ext fun x => by simp) }
  have hσb : ∀ c x, σb c (F.mkQ x) = F.mkQ (σ c x) := fun c x => rfl
  let πb : Module.End C (H ⧸ F) := F.mapQ F π (fun x hx => hπF x hx)
  have hπb : ∀ x, πb (F.mkQ x) = F.mkQ (π x) := fun x => rfl
  have hπσ : ∀ c, πb * σb c = σb c * πb := fun c => Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hσb, hπb]
    rw [← Module.End.mul_apply, ← hσπ c, Module.End.mul_apply])
  have hσσ : ∀ c d, σb c * σb d = σb d * σb c := fun c d => by
    rw [← map_mul, ← map_mul, mul_comm]
  obtain ⟨e, he1, he2, he3⟩ := GlobalTheory.T.exists_eigen_idempotents_of_comaximal σb a χ hχ
  have heπ : ∀ i, πb * e i = e i * πb := fun i => he1 i πb hπσ
  have heσ : ∀ i c, σb c * e i = e i * σb c := fun i c => he1 i (σb c) (hσσ c)
  have hππ : πb * πb = πb := Submodule.linearMap_qext _ (LinearMap.ext fun x => by
    simp only [LinearMap.comp_apply, Module.End.mul_apply, hπb]
    rw [← Module.End.mul_apply, hπ])

  have hD : ∀ x ∈ LinearMap.range π, ∃ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) ∧
      F.mkQ x = ∑ i, u i := by
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hdec x hx
    refine ⟨fun i => F.mkQ (w i), fun i c => ?_, ?_⟩
    · rw [hσb, ← map_smul, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 (hw1 i c)
    · rw [← map_sum, ← sub_eq_zero, ← map_sub]
      exact (Submodule.Quotient.mk_eq_zero F).2 hw2
  have hEu : ∀ x ∈ LinearMap.range π, ∀ u : Fin a → H ⧸ F, (∀ i c, σb c (u i) = χ i c • u i) →
      F.mkQ x = ∑ i, u i → ∀ i, e i (F.mkQ x) = u i := by
    intro x hx u hu hxu i
    rw [hxu, map_sum, Finset.sum_eq_single i]
    · exact he2 i (u i) (hu i)
    · intro j _ hji; exact he3 i j (u j) hji (hu j)
    · simp
  let p : Fin a → Module.End C (H ⧸ F) := fun i => e i * πb
  have hpx : ∀ i x, p i (F.mkQ x) = e i (F.mkQ (π x)) := fun i x => rfl
  have hpσ : ∀ i c, p i * σb c = σb c * p i := fun i c => by
    simp only [p]; rw [_root_.mul_assoc, hπσ, ← _root_.mul_assoc, ← heσ, _root_.mul_assoc]

  have hpE : ∀ i w, ∀ c, σb c (p i w) = χ i c • p i w := by
    intro i w c
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective F w
    obtain ⟨u, hu, hxu⟩ := hD (π x) (LinearMap.mem_range_self π x)
    rw [hpx, hEu _ (LinearMap.mem_range_self π x) u hu hxu]
    exact hu i c
  have hpe : ∀ i w, (∀ c, σb c w = χ i c • w) → e i (p i w) = p i w := fun i w _ => he2 i _ (hpE i w)
  have hpπ : ∀ i w, πb (p i w) = p i w := by
    intro i w
    simp only [p]
    rw [← Module.End.mul_apply, ← _root_.mul_assoc, heπ, _root_.mul_assoc, hππ]
  have hpp : ∀ i j w, p j (p i w) = if j = i then p i w else 0 := by
    intro i j w
    show e j (πb (p i w)) = _
    rw [hpπ]
    split_ifs with h
    · subst h; exact he2 j _ (hpE j w)
    · exact he3 j i _ (Ne.symm h) (hpE i w)
  have hidem : ∀ i, p i * p i = p i := fun i => LinearMap.ext fun w => by
    rw [Module.End.mul_apply, hpp]; simp
  choose n b f hb hfp hδ hinj using fun i => GlobalTheory.T.exists_coords_range_idempotent_of_retract I hItop m s r hrs (p i) (hidem i)
  obtain ⟨eqv⟩ : Nonempty ((Σ i, Fin (n i)) ≃ Fin (∑ i, n i)) := ⟨finSigmaFinEquiv⟩
  have hlift : ∀ i t, ∃ z ∈ LinearMap.range π, F.mkQ z = b i t := by
    intro i t
    obtain ⟨w, hw⟩ := hb i t
    obtain ⟨h', hh'⟩ := Submodule.mkQ_surjective F (e i w)
    refine ⟨π h', LinearMap.mem_range_self π h', ?_⟩
    rw [← hw, ← hπb, hh']
    show πb (e i w) = (e i * πb) w
    rw [← Module.End.mul_apply, heπ]
  choose z hz hzb using hlift
  let L : (Σ i, Fin (n i)) → H →ₗ[C] C ⧸ I := fun q => f q.1 q.2 ∘ₗ F.mkQ
  let Z : (Σ i, Fin (n i)) → H := fun q => z q.1 q.2
  have hL : ∀ i t x, L ⟨i, t⟩ x = f i t (F.mkQ x) := fun _ _ _ => rfl
  have hZ : ∀ i t, Z ⟨i, t⟩ = z i t := fun _ _ => rfl
  refine ⟨∑ i, n i, fun k => (eqv.symm k).1, fun k => L (eqv.symm k),
    fun k => Z (eqv.symm k), ?_, ?_, fun k => hz _ _, ?_⟩
  · intro k c x
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL]
    rw [← hσb, ← hfp i t, ← Module.End.mul_apply, hpσ, Module.End.mul_apply, hpE, map_smul, hfp,
      Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
  · intro x hx
    constructor
    · intro hxF k
      have h0 : F.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero F).2 hxF
      simp only [L, LinearMap.comp_apply, h0, map_zero]
    · intro hk
      obtain ⟨u, hu, hxu⟩ := hD x hx
      have hpu : ∀ i, p i (F.mkQ x) = u i := by
        intro i
        obtain ⟨x', rfl⟩ := hx
        have hx' : π (π x') = π x' := by rw [← Module.End.mul_apply, hπ]
        rw [hpx, hx']
        exact hEu _ (LinearMap.mem_range_self π x') u hu hxu i
      have h0 : ∀ i, u i = 0 := by
        intro i
        rw [← hpu i]
        refine hinj i _ (LinearMap.mem_range_self _ _) fun t => ?_
        rw [hfp]
        simpa [hL] using hk (eqv ⟨i, t⟩)
      rw [← Submodule.Quotient.mk_eq_zero F]
      change F.mkQ x = 0
      rw [hxu]; simp [h0]
  · intro j k
    obtain ⟨⟨i', t'⟩, rfl⟩ := eqv.surjective j
    obtain ⟨⟨i, t⟩, rfl⟩ := eqv.surjective k
    simp only [Equiv.symm_apply_apply, hL, hZ, hzb, eqv.injective.eq_iff]
    by_cases hii : i' = i
    · subst hii
      rw [hδ]
      simp
    · have : f i' t' (b i t) = 0 := by
        obtain ⟨w, hw⟩ := hb i t
        rw [← hfp, ← hw, hpp, if_neg hii, map_zero]
      rw [this, if_neg]
      intro h; exact hii (congrArg Sigma.fst h)

end GlobalTheory
