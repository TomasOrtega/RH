import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPairSplitSum
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginCut.TorsorField

/- English proof (translation)
Establish `hs : ∑ g, (Pi.single g (1 : A) : G → A) = 1`. Simplify using `using Finset.univ_sum_single (1 : G → A)`. Establish `hsum : ∑ g, z (Pi.single g 1) = 1` using `by rw [← map_sum, hs, map_one]`. Take `⟨g, -, hg⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := fun g => z (Pi.single g 1)) (by rw [hsum]; exact one_ne_zero)`. Establish `hidem : z (Pi.single g 1) = 1`.

Establish `h2 : z (Pi.single g 1) * z (Pi.single g 1) = z (Pi.single g 1) * 1`. Apply the tactic sequence `rw [← map_mul, mul_one]; congr 1; funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]`. Conclude with `mul_left_cancel₀ hg h2`. Use `⟨g, fun f => ?_⟩` and prove the remaining obligations. Establish `hf : f * Pi.single g 1 = (fun _ => f g) * Pi.single g 1`.

Apply the tactic sequence `funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_point_pi {K G A Ω : Type} [CommRing K] [Fintype G] [DecidableEq G] [CommRing A]
    [Algebra K A] [Field Ω] [Algebra K Ω] (z : (G → A) →ₐ[K] Ω) :
    ∃ g : G, ∀ f : G → A, z f = z (fun _ => f g) := by
  have hs : ∑ g, (Pi.single g (1 : A) : G → A) = 1 := by
    simpa using Finset.univ_sum_single (1 : G → A)
  have hsum : ∑ g, z (Pi.single g 1) = 1 := by rw [← map_sum, hs, map_one]
  obtain ⟨g, -, hg⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
    (f := fun g => z (Pi.single g 1)) (by rw [hsum]; exact one_ne_zero)
  have hidem : z (Pi.single g 1) = 1 := by
    have h2 : z (Pi.single g 1) * z (Pi.single g 1) = z (Pi.single g 1) * 1 := by
      rw [← map_mul, mul_one]; congr 1; funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
    exact mul_left_cancel₀ hg h2
  refine ⟨g, fun f => ?_⟩
  have hf : f * Pi.single g 1 = (fun _ => f g) * Pi.single g 1 := by
    funext h; by_cases hh : h = g <;> simp [Pi.single_apply, hh]
  calc z f = z f * z (Pi.single g 1) := by rw [hidem, mul_one]
    _ = z (fun _ => f g) * z (Pi.single g 1) := by rw [← map_mul, ← map_mul, hf]
    _ = z (fun _ => f g) := by rw [hidem, mul_one]

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

abbrev galMap (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) :
    M ⊗[K] M →ₐ[K] (Multiplicative (ZMod q) → M) :=
  Algebra.TensorProduct.productMap
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun _ => AlgHom.id K M))
    (Pi.algHom K (fun _ : Multiplicative (ZMod q) => M) (fun g => (act g).toAlgHom))

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `[galMap, Algebra.TensorProduct.productMap_apply_tmul]`.
-/
theorem galMap_tmul (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (a b : M) :
    galMap act (a ⊗ₜ b) = fun g => a * act g b := by
  funext g; simp [galMap, Algebra.TensorProduct.productMap_apply_tmul]

/- English proof (translation)
Set `Φ` to `AlgEquiv.ofBijective (galMap act) hbij`. Set `z` to `(Algebra.TensorProduct.productMap x y).comp Φ.symm.toAlgHom`. Take `⟨g, hg⟩` from `exists_point_pi z`. Establish `key : ∀ a b : M, x a * y b = z (fun _ => a * act g b)`. Introduce `a b`.

Establish `hΦ : Φ.symm (galMap act (a ⊗ₜ b)) = a ⊗ₜ b` using `by show Φ.symm (Φ (a ⊗ₜ b)) = _`. Conclude with `Φ.symm_apply_apply _`. Establish `h1 : z (galMap act (a ⊗ₜ b)) = x a * y b` using `by show Algebra.TensorProduct.productMap x y (Φ.symm (galMap act (a ⊗ₜ b))) = _`. Rewrite using `[hΦ, Algebra.TensorProduct.productMap_apply_tmul]`. Rewrite using `[← h1, hg, galMap_tmul]`.

Establish `hx : ∀ a, x a = z (fun _ => a)` using `fun a => by simpa using key a 1`. Use `⟨g, AlgHom.ext fun b => ?_⟩` and prove the remaining obligations. Establish `h` using `key 1 b`. Rewrite `h` using `[map_one, one_mul, one_mul]`. Rewrite using `[h, ← hx]`.

Both sides reduce to the same expression.
-/
theorem exists_eq_comp [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x y : M →ₐ[K] Ω) : ∃ g, y = x.comp (act g).toAlgHom := by
  classical
  let Φ := AlgEquiv.ofBijective (galMap act) hbij
  let z := (Algebra.TensorProduct.productMap x y).comp Φ.symm.toAlgHom
  obtain ⟨g, hg⟩ := exists_point_pi z
  have key : ∀ a b : M, x a * y b = z (fun _ => a * act g b) := by
    intro a b
    have hΦ : Φ.symm (galMap act (a ⊗ₜ b)) = a ⊗ₜ b := by
      show Φ.symm (Φ (a ⊗ₜ b)) = _
      exact Φ.symm_apply_apply _
    have h1 : z (galMap act (a ⊗ₜ b)) = x a * y b := by
      show Algebra.TensorProduct.productMap x y (Φ.symm (galMap act (a ⊗ₜ b))) = _
      rw [hΦ, Algebra.TensorProduct.productMap_apply_tmul]
    rw [← h1, hg, galMap_tmul]
  have hx : ∀ a, x a = z (fun _ => a) := fun a => by simpa using key a 1
  refine ⟨g, AlgHom.ext fun b => ?_⟩
  have h := key 1 b
  rw [map_one, one_mul, one_mul] at h
  rw [h, ← hx]; rfl

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Take `⟨w, hw⟩` from `hbij.2 (Pi.single g 1)`. Establish `hZ : ∀ k, Algebra.TensorProduct.productMap x (x.comp (act k).toAlgHom) = (x.comp (Pi.evalAlgHom K (fun _ => M) k)).comp (galMap act)`. Introduce `k`. Apply `Algebra.TensorProduct.ext'` to reduce the goal to its premises.

Introduce `a b`. Rewrite using `[AlgHom.comp_apply, galMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]`. Simplify using the standard rewrite rules. Establish `e1` using `congrArg (fun F => F w) (hZ g)`. Establish `e2` using `congrArg (fun F => F w) (hZ g')`.

Simplify using `only [AlgHom.comp_apply, hw, Pi.evalAlgHom_apply] at e1 e2`. Rewrite `e1` using `[h]`. Rewrite `e1` using `[Pi.single_eq_same]`. Rewrite `e2` using `[Pi.single_eq_of_ne (Ne.symm hne)]`. Use `e1.symm.trans e2` as an intermediate fact.

Simplify using `at this`.
-/
theorem eq_of_comp_eq [NeZero q] {Ω : Type} [Field Ω] [Algebra K Ω]
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)) (hbij : Function.Bijective (galMap act))
    (x : M →ₐ[K] Ω) {g g' : Multiplicative (ZMod q)}
    (h : x.comp (act g).toAlgHom = x.comp (act g').toAlgHom) : g = g' := by
  classical
  by_contra hne
  obtain ⟨w, hw⟩ := hbij.2 (Pi.single g 1)
  have hZ : ∀ k, Algebra.TensorProduct.productMap x (x.comp (act k).toAlgHom) =
      (x.comp (Pi.evalAlgHom K (fun _ => M) k)).comp (galMap act) := by
    intro k; apply Algebra.TensorProduct.ext'; intro a b
    rw [AlgHom.comp_apply, galMap_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    simp
  have e1 := congrArg (fun F => F w) (hZ g)
  have e2 := congrArg (fun F => F w) (hZ g')
  simp only [AlgHom.comp_apply, hw, Pi.evalAlgHom_apply] at e1 e2
  rw [h] at e1
  rw [Pi.single_eq_same] at e1
  rw [Pi.single_eq_of_ne (Ne.symm hne)] at e2
  have := e1.symm.trans e2
  simp at this

end GlobalTheory.KeyOriginCut.TorsorField

namespace GlobalTheory.KeyOriginCut.TorsorField

variable {K M : Type} [Field K] [CommRing M] [Algebra K M] {q : ℕ}

/- English proof (translation)
Set `Ω` to `AlgebraicClosure K`. Set `σ0 : L →ₐ[K] Ω` to `IsAlgClosed.lift`. Establish `hσ0inj : Function.Injective σ0` using `σ0.toRingHom.injective`. Set `P : Multiplicative (ZMod q) → Prop` to `fun g => ∀ a, π a = 0 → π (act g a) = 0`. Establish `hPmul : ∀ g h, P g → P h → P (g * h)`.

Introduce `g h hg hh a ha`. Rewrite using `[map_mul, AlgEquiv.mul_apply]`. Conclude with `hg _ (hh a ha)`. Establish `hPone : P 1` using `by intro a ha; rw [map_one, AlgEquiv.one_apply]; exact ha`. Establish `hPpow : ∀ g (n : ℕ), P g → P (g ^ n)`.

Introduce `g n hg`. Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `hPone`. Consider the case `succ n ih => rw [pow_succ]`.

Conclude with `hPmul _ _ ih hg`. Set `H : Subgroup (Multiplicative (ZMod q))` to `{ carrier := {g | P g} mul_mem' := fun {g h} hg hh => hPmul g h hg hh one_mem' := hPone inv_mem' := fun {g} hg => by show P g⁻¹`. Establish `hc : g ^ (Fintype.card (Multiplicative (ZMod q)) - 1) * g = 1`. Rewrite using `[← pow_succ, Nat.sub_add_cancel Fintype.card_pos, pow_card_eq_one]`. Rewrite using `[← eq_inv_of_mul_eq_one_left hc]`.

Conclude with `hPpow g _ hg }`. Establish `hτ : ∀ g, P g → ∃ τ : L →ₐ[K] L, τ.comp π = π.comp (act g).toAlgHom`. Introduce `g hg`. Set `E` to `Ideal.quotientKerAlgEquivOfSurjective hπ`. Set `f` to `Ideal.Quotient.liftₐ (RingHom.ker π) (π.comp (act g).toAlgHom) (fun a ha => hg a (RingHom.mem_ker.1 ha))`.

Use `⟨f.comp E.symm.toAlgHom, AlgHom.ext fun a => ?_⟩` and prove the remaining obligations. Establish `hE : E.symm (π a) = Ideal.Quotient.mk _ a` using `E.symm_apply_eq.2 rfl`. Use `show f (E.symm (π a)) = π (act g a)`. Rewrite using `[hE]`. Both sides reduce to the same expression.

Use `choose! τ hτc using hτ`. Establish `hΨ : ∀ g, P g → (σ0.comp (τ g)).comp π = (σ0.comp π).comp (act g).toAlgHom`. Introduce `g hg`. Rewrite using `[AlgHom.comp_assoc, hτc g hg, ← AlgHom.comp_assoc]`. Establish `hB : ∀ σ : L →ₐ[K] Ω, ∃ g, P g ∧ σ.comp π = (σ0.comp π).comp (act g).toAlgHom`.

Introduce `σ`. Take `⟨g, hg⟩` from `exists_eq_comp act hbij (σ0.comp π) (σ.comp π)`. Use `⟨g, fun a ha => hσ0inj ?_, hg⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun F => F a) hg`. Simplify using `only [AlgHom.comp_apply] at h`.

Rewrite using `[map_zero]; exact h.symm.trans (by rw [ha, map_zero])`. Establish `hcancel : ∀ σ σ' : L →ₐ[K] Ω, σ.comp π = σ'.comp π → σ = σ'`. Introduce `σ σ' h`. Use extensionality with `l`. Take `⟨a, rfl⟩` from `hπ l`.

Conclude with `congrArg (fun F => F a) h`. Set `Ψ : H → (L →ₐ[K] Ω)` to `fun g => σ0.comp (τ g)`. Establish `hΨbij : Function.Bijective Ψ`. Use `⟨fun g g' h => Subtype.ext ?_, fun σ => ?_⟩` and prove the remaining obligations. Establish `h2 : (σ0.comp π).comp (act g.1).toAlgHom = (σ0.comp π).comp (act g'.1).toAlgHom`.

Rewrite using `[← hΨ _ g.2, ← hΨ _ g'.2]`. Conclude with `congrArg (fun F => F.comp π) h`. Conclude with `eq_of_comp_eq act hbij _ h2`. Take `⟨g, hg, he⟩` from `hB σ`. Conclude with `⟨⟨g, hg⟩, hcancel _ _ ((hΨ g hg).trans he.symm)⟩`.

Establish `hcardΩ : Nat.card (L →ₐ[K] Ω) = Module.finrank K L`. Rewrite using `[Nat.card_eq_fintype_card, AlgHom.card]`. Establish `hcardH : Nat.card H = Module.finrank K L` using `(Nat.card_eq_of_bijective Ψ hΨbij).trans hcardΩ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hsurj : Function.Surjective (fun τ' : L →ₐ[K] L => σ0.comp τ')`.

Introduce `σ`. Take `⟨g, hg, he⟩` from `hB σ`. Conclude with `⟨τ g, hcancel _ _ ((hΨ g hg).trans he.symm)⟩`. Establish `hinj : Function.Injective (fun τ' : L →ₐ[K] L => σ0.comp τ')`. Introduce `a b h`.

Use extensionality with `l`. Conclude with `hσ0inj (congrArg (fun F => F l) h)`. Establish `hLL : Nat.card (L →ₐ[K] L) = Module.finrank K L` using `(Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).trans hcardΩ`. Apply `IsGalois.of_card_aut_eq_finrank` to reduce the goal to its premises. Rewrite using `[← hLL]`.

Conclude with `Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).toEquiv`. Rewrite using `[← hcardH]`. Use `Subgroup.card_subgroup_dvd_card H` as an intermediate fact. Simplify `this` using `[Nat.card_eq_fintype_card]`.
-/
theorem factor_isGalois_dvd [NeZero q] {L : Type} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M))
    (hbij : Function.Bijective (galMap act)) (π : M →ₐ[K] L) (hπ : Function.Surjective π) :
    IsGalois K L ∧ Module.finrank K L ∣ q := by
  classical
  let Ω := AlgebraicClosure K
  let σ0 : L →ₐ[K] Ω := IsAlgClosed.lift
  have hσ0inj : Function.Injective σ0 := σ0.toRingHom.injective
  let P : Multiplicative (ZMod q) → Prop := fun g => ∀ a, π a = 0 → π (act g a) = 0
  have hPmul : ∀ g h, P g → P h → P (g * h) := by
    intro g h hg hh a ha; rw [map_mul, AlgEquiv.mul_apply]; exact hg _ (hh a ha)
  have hPone : P 1 := by intro a ha; rw [map_one, AlgEquiv.one_apply]; exact ha
  have hPpow : ∀ g (n : ℕ), P g → P (g ^ n) := by
    intro g n hg; induction n with
    | zero => rw [pow_zero]; exact hPone
    | succ n ih => rw [pow_succ]; exact hPmul _ _ ih hg
  let H : Subgroup (Multiplicative (ZMod q)) :=
    { carrier := {g | P g}
      mul_mem' := fun {g h} hg hh => hPmul g h hg hh
      one_mem' := hPone
      inv_mem' := fun {g} hg => by
        show P g⁻¹
        have hc : g ^ (Fintype.card (Multiplicative (ZMod q)) - 1) * g = 1 := by
          rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos, pow_card_eq_one]
        rw [← eq_inv_of_mul_eq_one_left hc]
        exact hPpow g _ hg }
  have hτ : ∀ g, P g → ∃ τ : L →ₐ[K] L, τ.comp π = π.comp (act g).toAlgHom := by
    intro g hg
    let E := Ideal.quotientKerAlgEquivOfSurjective hπ
    let f := Ideal.Quotient.liftₐ (RingHom.ker π) (π.comp (act g).toAlgHom)
      (fun a ha => hg a (RingHom.mem_ker.1 ha))
    refine ⟨f.comp E.symm.toAlgHom, AlgHom.ext fun a => ?_⟩
    have hE : E.symm (π a) = Ideal.Quotient.mk _ a := E.symm_apply_eq.2 rfl
    show f (E.symm (π a)) = π (act g a)
    rw [hE]; rfl
  choose! τ hτc using hτ
  have hΨ : ∀ g, P g → (σ0.comp (τ g)).comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro g hg; rw [AlgHom.comp_assoc, hτc g hg, ← AlgHom.comp_assoc]
  have hB : ∀ σ : L →ₐ[K] Ω, ∃ g, P g ∧ σ.comp π = (σ0.comp π).comp (act g).toAlgHom := by
    intro σ
    obtain ⟨g, hg⟩ := exists_eq_comp act hbij (σ0.comp π) (σ.comp π)
    refine ⟨g, fun a ha => hσ0inj ?_, hg⟩
    have h := congrArg (fun F => F a) hg
    simp only [AlgHom.comp_apply] at h
    rw [map_zero]; exact h.symm.trans (by rw [ha, map_zero])
  have hcancel : ∀ σ σ' : L →ₐ[K] Ω, σ.comp π = σ'.comp π → σ = σ' := by
    intro σ σ' h; ext l; obtain ⟨a, rfl⟩ := hπ l
    exact congrArg (fun F => F a) h

  let Ψ : H → (L →ₐ[K] Ω) := fun g => σ0.comp (τ g)
  have hΨbij : Function.Bijective Ψ := by
    refine ⟨fun g g' h => Subtype.ext ?_, fun σ => ?_⟩
    · have h2 : (σ0.comp π).comp (act g.1).toAlgHom = (σ0.comp π).comp (act g'.1).toAlgHom := by
        rw [← hΨ _ g.2, ← hΨ _ g'.2]; exact congrArg (fun F => F.comp π) h
      exact eq_of_comp_eq act hbij _ h2
    · obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨⟨g, hg⟩, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
  have hcardΩ : Nat.card (L →ₐ[K] Ω) = Module.finrank K L := by
    rw [Nat.card_eq_fintype_card, AlgHom.card]
  have hcardH : Nat.card H = Module.finrank K L := (Nat.card_eq_of_bijective Ψ hΨbij).trans hcardΩ
  refine ⟨?_, ?_⟩
  ·
    have hsurj : Function.Surjective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro σ
      obtain ⟨g, hg, he⟩ := hB σ
      exact ⟨τ g, hcancel _ _ ((hΨ g hg).trans he.symm)⟩
    have hinj : Function.Injective (fun τ' : L →ₐ[K] L => σ0.comp τ') := by
      intro a b h; ext l; exact hσ0inj (congrArg (fun F => F l) h)
    have hLL : Nat.card (L →ₐ[K] L) = Module.finrank K L :=
      (Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩).trans hcardΩ
    apply IsGalois.of_card_aut_eq_finrank
    rw [← hLL]
    exact Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom K L).toEquiv
  · rw [← hcardH]
    have := Subgroup.card_subgroup_dvd_card H
    simpa [Nat.card_eq_fintype_card] using this

end GlobalTheory.KeyOriginCut.TorsorField

open GlobalTheory.KeyOriginCut.TorsorField in

/- English proof (translation)
Introduce `K M _ _ _ q act hq htor`. Use `haveI : NeZero q := ⟨hq.ne'⟩`. Use `haveI : Algebra.Etale K M := GlobalTheory.KeyOriginCut.etale_of_isZTorsor K M q act htor`. Take `⟨I, hI, L, hF, hA, e, hL⟩` from `(Algebra.Etale.iff_exists_algEquiv_prod K M).1 inferInstance`. Establish `hbij : Function.Bijective (galMap act)` using `htor.2.2.2`.

Establish `key : ∀ i, IsGalois K (L i) ∧ Module.finrank K (L i) ∣ q`. Introduce `i`. Use `haveI := (hL i).1`. Use `haveI := (hL i).2`. Conclude with `factor_isGalois_dvd act hbij ((Pi.evalAlgHom K L i).comp e.toAlgHom) ((Function.surjective_eval i).comp e.surjective)`.

Conclude with `⟨I, Fintype.ofFinite I, L, hF, hA, fun i => (hL i).1, fun i => (key i).1, fun i => (key i).2, ⟨e⟩⟩`.
-/
theorem GlobalTheory.KeyOriginCut.torsor_field_eq_prod_galois :
    ∀ (K M : Type) [Field K] [CommRing M] [Algebra K M] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)), 0 < q →
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    ∃ (ι : Type) (_ : Fintype ι) (L : ι → Type) (_ : ∀ i, Field (L i)) (_ : ∀ i, Algebra K (L i)),
      (∀ i, FiniteDimensional K (L i)) ∧ (∀ i, IsGalois K (L i)) ∧
      (∀ i, Module.finrank K (L i) ∣ q) ∧ Nonempty (M ≃ₐ[K] ∀ i, L i) := by
  intro K M _ _ _ q act hq htor
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : Algebra.Etale K M := GlobalTheory.KeyOriginCut.etale_of_isZTorsor K M q act htor
  obtain ⟨I, hI, L, hF, hA, e, hL⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K M).1 inferInstance
  have hbij : Function.Bijective (galMap act) := htor.2.2.2
  have key : ∀ i, IsGalois K (L i) ∧ Module.finrank K (L i) ∣ q := by
    intro i
    haveI := (hL i).1
    haveI := (hL i).2
    exact factor_isGalois_dvd act hbij ((Pi.evalAlgHom K L i).comp e.toAlgHom)
      ((Function.surjective_eval i).comp e.surjective)
  exact ⟨I, Fintype.ofFinite I, L, hF, hA, fun i => (hL i).1, fun i => (key i).1,
    fun i => (key i).2, ⟨e⟩⟩
