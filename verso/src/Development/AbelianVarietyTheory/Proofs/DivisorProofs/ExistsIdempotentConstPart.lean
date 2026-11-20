import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOCStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupResidueFieldTateLevelSectionStatement

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

open TensorProduct Coalgebra Bialgebra WithConv

namespace GlobalTheory.ConstPart

open Classical

variable {O : Type} [CommRing O] [IsLocalRing O]

def IdemData (A : Type) [CommRing A] [Algebra O A]
    (e : (A →ₐ[O] IsLocalRing.ResidueField O) → A) : Prop :=
  (∀ c, IsIdempotentElem (e c)) ∧ (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧
    ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c'

def HasIdem (O : Type) [CommRing O] [IsLocalRing O] : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A],
    Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, IdemData A e

section Idem

variable {A : Type} [CommRing A] [Algebra O A] {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A}

/- English proof (translation)
Use `split_ifs with h`. Conclude with `(he.2.2.2 c c').2 h`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map c') with h0 | h1` into its components or cases. Conclude with `h0`. Conclude with `absurd ((he.2.2.2 c c').1 h1) h`.
-/
theorem IdemData.pt (he : IdemData A e) (c c' : A →ₐ[O] IsLocalRing.ResidueField O) :
    c' (e c) = if c = c' then 1 else 0 := by
  split_ifs with h
  · exact (he.2.2.2 c c').2 h
  · rcases IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map c') with h0 | h1
    · exact h0
    · exact absurd ((he.2.2.2 c c').1 h1) h

/- English proof (translation)
Establish `h` using `he.pt c ((Algebra.ofId O (IsLocalRing.ResidueField O)).comp x)`. Rewrite `h` using `[AlgHom.comp_apply]`. Break down `IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map x) with h0 | h1` into its components or cases. Rewrite `h` using `[h0, map_zero]`. Rewrite using `[h0]`.

Use `split_ifs at h ⊢ with hc`. Conclude with `absurd h.symm one_ne_zero`. Both sides reduce to the same expression. Rewrite `h` using `[h1, map_one]`. Rewrite using `[h1]`.

Use `split_ifs at h ⊢ with hc`. Both sides reduce to the same expression. Conclude with `absurd h one_ne_zero`.
-/
theorem IdemData.ptO [IsDomain O] (he : IdemData A e) (c : A →ₐ[O] IsLocalRing.ResidueField O)
    (x : A →ₐ[O] O) :
    x (e c) = if c = (Algebra.ofId O (IsLocalRing.ResidueField O)).comp x then 1 else 0 := by
  have h := he.pt c ((Algebra.ofId O (IsLocalRing.ResidueField O)).comp x)
  rw [AlgHom.comp_apply] at h
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 ((he.1 c).map x) with h0 | h1
  · rw [h0, map_zero] at h
    rw [h0]
    split_ifs at h ⊢ with hc
    · exact absurd h.symm one_ne_zero
    · rfl
  · rw [h1, map_one] at h
    rw [h1]
    split_ifs at h ⊢ with hc
    · rfl
    · exact absurd h one_ne_zero

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Conclude with `(he.1 c).eq`. Conclude with `he.2.1 c c' h`.
-/
theorem IdemData.mul_eq (he : IdemData A e) (c c' : A →ₐ[O] IsLocalRing.ResidueField O) :
    e c * e c' = if c = c' then e c else 0 := by
  split_ifs with h
  · subst h; exact (he.1 c).eq
  · exact he.2.1 c c' h

/- English proof (translation)
Rewrite using `[← finsum_eq_sum_of_fintype]`. Conclude with `he.2.2.1`.
-/
theorem IdemData.sum_eq [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)] (he : IdemData A e) :
    ∑ c, e c = 1 := by
  rw [← finsum_eq_sum_of_fintype]; exact he.2.2.1

end Idem

/- English proof (translation)
Unfold `IsIdempotentElem`. Rewrite using `[Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Repeatedly rewrite using `[ite_mul, mul_ite, mul_zero, zero_mul, hf]`. Use `split_ifs with hi`.

Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]`. Simplify using `[hi]`. Simplify using the standard rewrite rules.
-/
theorem isIdempotentElem_sum_ite {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (f : ι → R) (hf : ∀ i j, f i * f j = if i = j then f i else 0) (q : ι → Prop)
    [DecidablePred q] : IsIdempotentElem (∑ i, if q i then f i else 0) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp_rw [ite_mul, mul_ite, mul_zero, zero_mul, hf]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp [hi]
  · simp

/- English proof (translation)
Use `set I : Ideal A := Ideal.span {1 - g}`. Use `haveI : Module.Finite O (A ⧸ I) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ O I).toLinearMap (Ideal.Quotient.mkₐ_surjective O I)`. Take `⟨-, e, -, -, hsum, -⟩` from `H (A ⧸ I)`. Establish `hE : IsEmpty ((A ⧸ I) →ₐ[O] IsLocalRing.ResidueField O)` using `⟨fun d => by`. Establish `h1 : d (Ideal.Quotient.mk I (1 - g)) = 0`.

Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]`. Establish `h2` using `h (d.comp (Ideal.Quotient.mkₐ O I))`. Rewrite `h2` using `[AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]`. Rewrite `h1` using `[map_sub, map_one, map_sub, map_one, h2, sub_zero]`. Conclude with `one_ne_zero h1⟩`.

Rewrite `hsum` using `[finsum_of_isEmpty]`. Establish `h1 : (1 : A) ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_one]`. Conclude with `hsum.symm`. Take `⟨b, hb⟩` from `Ideal.mem_span_singleton'.1 h1`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem idem_eq_zero (H : HasIdem O) {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A]
    {g : A} (hg : IsIdempotentElem g)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c g = 0) : g = 0 := by
  set I : Ideal A := Ideal.span {1 - g}
  haveI : Module.Finite O (A ⧸ I) := Module.Finite.of_surjective
    (Ideal.Quotient.mkₐ O I).toLinearMap (Ideal.Quotient.mkₐ_surjective O I)
  obtain ⟨-, e, -, -, hsum, -⟩ := H (A ⧸ I)
  have hE : IsEmpty ((A ⧸ I) →ₐ[O] IsLocalRing.ResidueField O) := ⟨fun d => by
    have h1 : d (Ideal.Quotient.mk I (1 - g)) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
    have h2 := h (d.comp (Ideal.Quotient.mkₐ O I))
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [map_sub, map_one, map_sub, map_one, h2, sub_zero] at h1
    exact one_ne_zero h1⟩
  rw [finsum_of_isEmpty] at hsum
  have h1 : (1 : A) ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_one]; exact hsum.symm
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h1
  calc g = b * (1 - g) * g := by rw [hb, one_mul]
    _ = b * (g - g * g) := by ring
    _ = 0 := by rw [hg.eq, sub_self, mul_zero]

/- English proof (translation)
Establish `key : ∀ a b : A, IsIdempotentElem a → IsIdempotentElem b → (∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c a = c b) → a * (1 - b) = 0`. Introduce `a b ha hb hab`. Use `idem_eq_zero H (ha.mul hb.one_sub) fun c => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_sub, map_one, hab c, mul_sub, mul_one, (hb.map c).eq, sub_self]`. Establish `h1` using `key f g hf hg h`.

Establish `h2` using `key g f hg hf fun c => (h c).symm`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem idem_eq (H : HasIdem O) {A : Type} [CommRing A] [Algebra O A] [Module.Finite O A]
    {f g : A} (hf : IsIdempotentElem f) (hg : IsIdempotentElem g)
    (h : ∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c f = c g) : f = g := by
  have key : ∀ a b : A, IsIdempotentElem a → IsIdempotentElem b →
      (∀ c : A →ₐ[O] IsLocalRing.ResidueField O, c a = c b) → a * (1 - b) = 0 := by
    intro a b ha hb hab
    refine idem_eq_zero H (ha.mul hb.one_sub) fun c => ?_
    rw [map_mul, map_sub, map_one, hab c, mul_sub, mul_one, (hb.map c).eq, sub_self]
  have h1 := key f g hf hg h
  have h2 := key g f hg hf fun c => (h c).symm
  calc f = f * g := by rw [mul_sub, mul_one, sub_eq_zero] at h1; exact h1
    _ = g * f := mul_comm _ _
    _ = g := by rw [mul_sub, mul_one, sub_eq_zero] at h2; exact h2.symm

section Sum

variable {A : Type} [CommRing A] [Algebra O A] {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A}
  [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)]

def sumE (he : IdemData A e) : ((A →ₐ[O] IsLocalRing.ResidueField O) → O) →ₐ[O] A where
  toFun f := ∑ c, f c • e c
  map_one' := by simp only [Pi.one_apply, one_smul]; exact he.sum_eq
  map_mul' f g := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp_rw [smul_mul_smul_comm, he.mul_eq, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq]
    simp [Pi.mul_apply]
  map_zero' := by simp
  map_add' f g := by simp [add_smul, Finset.sum_add_distrib]
  commutes' r := by
    simp only [Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [← Finset.smul_sum, he.sum_eq, Algebra.algebraMap_eq_smul_one]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sumE_apply (he : IdemData A e) (f : (A →ₐ[O] IsLocalRing.ResidueField O) → O) :
    sumE he f = ∑ c, f c • e c := rfl

end Sum

/- English proof (translation)
Use `idem_eq H ((he.1 c).map φ) (isIdempotentElem_sum_ite e' he'.mul_eq _) fun d => ?_` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_apply, he.pt, map_sum]`. Repeatedly rewrite using `[apply_ite d, map_zero, he'.pt]`. Rewrite using `[Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]`. Simplify using `[eq_comm]`.
-/
theorem push_e (H : HasIdem O) {A A' : Type} [CommRing A] [Algebra O A] [CommRing A']
    [Algebra O A'] [Module.Finite O A'] [Fintype (A' →ₐ[O] IsLocalRing.ResidueField O)]
    {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A} {e' : (A' →ₐ[O] IsLocalRing.ResidueField O) → A'}
    (he : IdemData A e) (he' : IdemData A' e') (φ : A →ₐ[O] A')
    (c : A →ₐ[O] IsLocalRing.ResidueField O) :
    φ (e c) = ∑ c', if c'.comp φ = c then e' c' else 0 := by
  refine idem_eq H ((he.1 c).map φ) (isIdempotentElem_sum_ite e' he'.mul_eq _) fun d => ?_
  rw [← AlgHom.comp_apply, he.pt, map_sum]
  simp_rw [apply_ite d, map_zero, he'.pt]
  rw [Finset.sum_eq_single d (fun b _ hb => by simp [hb]) (by simp)]
  simp [eq_comm]

/- English proof (translation)
Establish `horth : ∀ x y : (A →ₐ[O] IsLocalRing.ResidueField O) × (A →ₐ[O] IsLocalRing.ResidueField O), (e x.1 ⊗ₜ[O] e x.2) * (e y.1 ⊗ₜ[O] e y.2) = if x = y then e x.1 ⊗ₜ[O] e x.2 else 0`. Introduce `x y`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, he.mul_eq, he.mul_eq]`. Apply the tactic sequence `by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2, Prod.ext_iff]`. Establish `hc : comul (R` using `O) (e c) = comulAlgHom O A (e c) := rfl`.

Rewrite using `[hc]`. Use `idem_eq H ((he.1 c).map _) (isIdempotentElem_sum_ite _ horth _) fun d => ?_` and prove the remaining obligations. Use `set d₁ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeLeft`. Use `set d₂ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeRight`. Establish `hd : Algebra.TensorProduct.lift d₁ d₂ (fun _ _ => .all _ _) = d` using `Algebra.TensorProduct.ext' fun a b => by`.

Rewrite using `[Algebra.TensorProduct.lift_tmul]`. Simplify using `only [d₁, d₂, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`. Establish `hdt : ∀ a b : A, d (a ⊗ₜ[O] b) = d₁ a * d₂ b` using `fun a b => by`. Rewrite using `[← hd, Algebra.TensorProduct.lift_tmul]`. Establish `hl : d (comulAlgHom O A (e c)) = ofConv (toConv d₁ * toConv d₂) (e c)`.

Rewrite using `[AlgHom.convMul_apply, hd]`. Both sides reduce to the same expression. Rewrite using `[hl, he.pt, map_sum]`. Repeatedly rewrite using `[apply_ite d, map_zero, hdt, he.pt]`. Rewrite using `[Finset.sum_eq_single (d₁, d₂) (fun b _ hb => by`.

Apply the tactic sequence `by_cases h1 : b.1 = d₁ <;> by_cases h2 : b.2 = d₂ <;> simp_all [Prod.ext_iff]) (by simp)]`. Simplify using `[eq_comm]`.
-/
theorem comul_e (H : HasIdem O) {A : Type} [CommRing A] [Bialgebra O A] [Module.Finite O A]
    [Fintype (A →ₐ[O] IsLocalRing.ResidueField O)]
    {e : (A →ₐ[O] IsLocalRing.ResidueField O) → A} (he : IdemData A e)
    (c : A →ₐ[O] IsLocalRing.ResidueField O) :
    comul (R := O) (e c) = ∑ x : (A →ₐ[O] IsLocalRing.ResidueField O) ×
      (A →ₐ[O] IsLocalRing.ResidueField O),
      if ofConv (toConv x.1 * toConv x.2) = c then e x.1 ⊗ₜ[O] e x.2 else 0 := by
  have horth : ∀ x y : (A →ₐ[O] IsLocalRing.ResidueField O) × (A →ₐ[O] IsLocalRing.ResidueField O),
      (e x.1 ⊗ₜ[O] e x.2) * (e y.1 ⊗ₜ[O] e y.2) = if x = y then e x.1 ⊗ₜ[O] e x.2 else 0 := by
    intro x y
    rw [Algebra.TensorProduct.tmul_mul_tmul, he.mul_eq, he.mul_eq]
    by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;> simp [h1, h2, Prod.ext_iff]
  have hc : comul (R := O) (e c) = comulAlgHom O A (e c) := rfl
  rw [hc]
  refine idem_eq H ((he.1 c).map _) (isIdempotentElem_sum_ite _ horth _) fun d => ?_
  set d₁ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeLeft
  set d₂ : A →ₐ[O] IsLocalRing.ResidueField O := d.comp Algebra.TensorProduct.includeRight
  have hd : Algebra.TensorProduct.lift d₁ d₂ (fun _ _ => .all _ _) = d :=
    Algebra.TensorProduct.ext' fun a b => by
      rw [Algebra.TensorProduct.lift_tmul]
      simp only [d₁, d₂, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
        Algebra.TensorProduct.includeRight_apply, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
        mul_one, one_mul]
  have hdt : ∀ a b : A, d (a ⊗ₜ[O] b) = d₁ a * d₂ b := fun a b => by
    rw [← hd, Algebra.TensorProduct.lift_tmul]
  have hl : d (comulAlgHom O A (e c)) = ofConv (toConv d₁ * toConv d₂) (e c) := by
    rw [AlgHom.convMul_apply, hd]; rfl
  rw [hl, he.pt, map_sum]
  simp_rw [apply_ite d, map_zero, hdt, he.pt]
  rw [Finset.sum_eq_single (d₁, d₂) (fun b _ hb => by
    by_cases h1 : b.1 = d₁ <;> by_cases h2 : b.2 = d₂ <;> simp_all [Prod.ext_iff]) (by simp)]
  simp [eq_comm]

section Group

variable {p : ℕ} [Fact p.Prime] [IsDomain O] (G : PDivGroup p O)
  (s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate)
  (hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c)

def sig (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) : G.A n →ₐ[O] O :=
  (s (Classical.choose (hpt n c))).pt n

variable {G s hpt}
variable (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)

include hw in
/- English proof (translation)
The claim follows from `hw n _ _ (Classical.choose_spec (hpt n (t.pt n)))`.
-/
theorem sig_eq (n : ℕ) (t : G.TateOver (IsLocalRing.ResidueField O)) :
    sig G s hpt n (t.pt n) = (s t).pt n :=
  hw n _ _ (Classical.choose_spec (hpt n (t.pt n)))

include hs hw in
/- English proof (translation)
Take `⟨t, rfl⟩` from `hpt n c`. Rewrite using `[sig_eq hw]`. Conclude with `congrArg (fun y => TateOver.pt y n) (hs t)`.
-/
theorem ofId_comp_sig (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    (Algebra.ofId O (IsLocalRing.ResidueField O)).comp (sig G s hpt n c) = c := by
  obtain ⟨t, rfl⟩ := hpt n c
  rw [sig_eq hw]
  exact congrArg (fun y => TateOver.pt y n) (hs t)

include hw in
/- English proof (translation)
Take `⟨t₁, rfl⟩` from `hpt n c₁`. Take `⟨t₂, rfl⟩` from `hpt n c₂`. Establish `h : ofConv (toConv (t₁.pt n) * toConv (t₂.pt n)) = (t₁ + t₂).pt n` using `rfl`. Rewrite using `[h, sig_eq hw, sig_eq hw, sig_eq hw, map_add]`. Both sides reduce to the same expression.
-/
theorem sig_mul (n : ℕ) (c₁ c₂ : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    sig G s hpt n (ofConv (toConv c₁ * toConv c₂)) =
      ofConv (toConv (sig G s hpt n c₁) * toConv (sig G s hpt n c₂)) := by
  obtain ⟨t₁, rfl⟩ := hpt n c₁
  obtain ⟨t₂, rfl⟩ := hpt n c₂
  have h : ofConv (toConv (t₁.pt n) * toConv (t₂.pt n)) = (t₁ + t₂).pt n := rfl
  rw [h, sig_eq hw, sig_eq hw, sig_eq hw, map_add]
  rfl

include hw in
/- English proof (translation)
Establish `h : ofConv (1 : WithConv (G.A n →ₐ[O] IsLocalRing.ResidueField O)) = (0 : G.TateOver (IsLocalRing.ResidueField O)).pt n` using `rfl`. Rewrite using `[h, sig_eq hw, map_zero]`. Both sides reduce to the same expression.
-/
theorem sig_one (n : ℕ) :
    sig G s hpt n (ofConv (1 : WithConv (G.A n →ₐ[O] IsLocalRing.ResidueField O))) =
      ofConv (1 : WithConv (G.A n →ₐ[O] O)) := by
  have h : ofConv (1 : WithConv (G.A n →ₐ[O] IsLocalRing.ResidueField O)) =
    (0 : G.TateOver (IsLocalRing.ResidueField O)).pt n := rfl
  rw [h, sig_eq hw, map_zero]
  rfl

omit [IsLocalRing O] [IsDomain O] in

/- English proof (translation)
Establish `h1 : ((p : ℤ_[p]) • x).conv (n + 1) = x.conv (n + 1) ^ p`. Rewrite using `[TateOver.smul_conv]`. Conclude with `GlobalTheory.PDiv.pow_digit_natCast (G.pts_pow_self (n + 1) _) p`. Conclude with `congrArg ofConv (h1.trans (x.conv_succ_pow n))`.
-/
theorem smul_p_pt {B : Type} [CommRing B] [Algebra O B] (x : G.TateOver B) (n : ℕ) :
    ((p : ℤ_[p]) • x).pt (n + 1) = (x.pt n).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
  have h1 : ((p : ℤ_[p]) • x).conv (n + 1) = x.conv (n + 1) ^ p := by
    rw [TateOver.smul_conv]
    exact GlobalTheory.PDiv.pow_digit_natCast (G.pts_pow_self (n + 1) _) p
  exact congrArg ofConv (h1.trans (x.conv_succ_pow n))

include hw in
/- English proof (translation)
Take `⟨t, rfl⟩` from `hpt n c`. Rewrite using `[← smul_p_pt, sig_eq hw, map_smul, smul_p_pt, sig_eq hw]`.
-/
theorem sig_res (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) :
    sig G s hpt (n + 1) (c.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n)) =
      (sig G s hpt n c).comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) := by
  obtain ⟨t, rfl⟩ := hpt n c
  rw [← smul_p_pt, sig_eq hw, map_smul, smul_p_pt, sig_eq hw]

end Group

section Endo

variable {p : ℕ} [Fact p.Prime] [IsDomain O] {G : PDivGroup p O}
  {s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate}
  {hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c}
  (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)
  [∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O)]
  {e : ∀ n, (G.A n →ₐ[O] IsLocalRing.ResidueField O) → G.A n} (he : ∀ n, IdemData (G.A n) (e n))

variable (s hpt) in

def endo (n : ℕ) : G.A n →ₐ[O] G.A n :=
  (sumE (he n)).comp (AlgHom.pi (sig G s hpt n))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem endo_apply (n : ℕ) (a : G.A n) :
    endo s hpt he n a = ∑ c, sig G s hpt n c a • e n c := rfl

include hs hw in
/- English proof (translation)
Rewrite using `[sumE_apply, map_sum]`. Repeatedly rewrite using `[map_smul, (he n).ptO, ofId_comp_sig hs hw]`. Simplify using the standard rewrite rules.
-/
theorem sig_sumE (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O)
    (f : (G.A n →ₐ[O] IsLocalRing.ResidueField O) → O) :
    sig G s hpt n c (sumE (he n) f) = f c := by
  rw [sumE_apply, map_sum]
  simp_rw [map_smul, (he n).ptO, ofId_comp_sig hs hw]
  simp

include hs hw in
/- English proof (translation)
Establish `h : AlgHom.pi (sig G s hpt n) (sumE (he n) f) = f`. Use function extensionality and compare the values at `fun c => sig_sumE hs hw he n c f`. Express the relevant statement in the definitionally equal form `sumE (he n) (AlgHom.pi (sig G s hpt n) (sumE (he n) f)) = _`. Rewrite using `[h]`.
-/
theorem endo_sumE (n : ℕ) (f : (G.A n →ₐ[O] IsLocalRing.ResidueField O) → O) :
    endo s hpt he n (sumE (he n) f) = sumE (he n) f := by
  have h : AlgHom.pi (sig G s hpt n) (sumE (he n) f) = f :=
    funext fun c => sig_sumE hs hw he n c f
  change sumE (he n) (AlgHom.pi (sig G s hpt n) (sumE (he n) f)) = _
  rw [h]

include hs hw in
/- English proof (translation)
The claim follows from `endo_sumE hs hw he n _`.
-/
theorem endo_endo (n : ℕ) (a : G.A n) : endo s hpt he n (endo s hpt he n a) = endo s hpt he n a :=
  endo_sumE hs hw he n _

include hs hw in
/- English proof (translation)
Use extensionality with `a`. Rewrite using `[AlgHom.comp_apply, endo_apply, map_sum]`. Repeatedly rewrite using `[map_smul, (he n).ptO]`. Simplify using `only [smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using `only [Finset.mem_univ, if_true]`. Establish `h` using `congrArg (fun x : G.A n →ₐ[O] O => x a) (sig_one (hpt := hpt) hw n)`. Conclude with `h`.
-/
theorem counit_endo (n : ℕ) :
    (counitAlgHom O (G.A n)).comp (endo s hpt he n) = counitAlgHom O (G.A n) := by
  ext a
  rw [AlgHom.comp_apply, endo_apply, map_sum]
  simp_rw [map_smul, (he n).ptO]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have h := congrArg (fun x : G.A n →ₐ[O] O => x a) (sig_one (hpt := hpt) hw n)
  exact h

end Endo

section Endo2

variable {p : ℕ} [Fact p.Prime] [IsDomain O] {G : PDivGroup p O}
  {s : G.TateOver (IsLocalRing.ResidueField O) →ₗ[ℤ_[p]] G.Tate}
  {hpt : ∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O),
    ∃ t : G.TateOver (IsLocalRing.ResidueField O), t.pt n = c}
  (hs : ∀ t, G.tatePush (Algebra.ofId O (IsLocalRing.ResidueField O)) (s t) = t)
  (hw : ∀ (n : ℕ) (t t' : G.TateOver (IsLocalRing.ResidueField O)),
    t.pt n = t'.pt n → (s t).pt n = (s t').pt n)
  [∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O)]
  {e : ∀ n, (G.A n →ₐ[O] IsLocalRing.ResidueField O) → G.A n} (he : ∀ n, IdemData (G.A n) (e n))

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a b`. Rewrite using `[Algebra.TensorProduct.map_tmul, endo_apply, endo_apply, TensorProduct.sum_tmul, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun c₁ _ => ?_` and prove the remaining obligations.

Rewrite using `[TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun c₂ _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.lift_tmul, TensorProduct.smul_tmul_smul]`. Consider the case `add x y hx hy`. Simplify using `only [map_add, hx, hy, add_smul, Finset.sum_add_distrib]`.
-/
theorem map_endo_endo (n : ℕ) (z : G.A n ⊗[O] G.A n) :
    Algebra.TensorProduct.map (endo s hpt he n) (endo s hpt he n) z =
      ∑ x : (G.A n →ₐ[O] IsLocalRing.ResidueField O) × (G.A n →ₐ[O] IsLocalRing.ResidueField O),
        Algebra.TensorProduct.lift (sig G s hpt n x.1) (sig G s hpt n x.2) (fun _ _ => .all _ _) z •
          (e n x.1 ⊗ₜ[O] e n x.2) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [Algebra.TensorProduct.map_tmul, endo_apply, endo_apply, TensorProduct.sum_tmul,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun c₁ _ => ?_
    rw [TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c₂ _ => ?_
    rw [Algebra.TensorProduct.lift_tmul, TensorProduct.smul_tmul_smul]
  | add x y hx hy =>
    simp only [map_add, hx, hy, add_smul, Finset.sum_add_distrib]

include hw in
/- English proof (translation)
Use `AlgHom.ext fun a => ?_` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, AlgHom.comp_apply, map_endo_endo, endo_apply, map_sum]`. Repeatedly rewrite using `[map_smul, Bialgebra.comulAlgHom_apply, comul_e H (he n), Finset.smul_sum, smul_ite, smul_zero]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_univ, if_true]`. Rewrite using `[sig_mul hw]`. Use `congr 1`. Conclude with `(AlgHom.convMul_apply _ _ a).symm`.
-/
theorem comul_endo (H : HasIdem O) (n : ℕ) :
    (Algebra.TensorProduct.map (endo s hpt he n) (endo s hpt he n)).comp
      (comulAlgHom O (G.A n)) = (comulAlgHom O (G.A n)).comp (endo s hpt he n) := by
  refine AlgHom.ext fun a => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, map_endo_endo, endo_apply, map_sum]
  simp_rw [map_smul, Bialgebra.comulAlgHom_apply, comul_e H (he n), Finset.smul_sum, smul_ite,
    smul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [sig_mul hw]
  congr 1
  exact (AlgHom.convMul_apply _ _ a).symm

include hw in
/- English proof (translation)
Establish `hp : ∀ c, G.res n (e (n + 1) c) = ∑ c', if c'.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) = c then e n c' else 0` using `fun c => by`. Conclude with `push_e H (he (n + 1)) (he n) (G.res n : G.A (n + 1) →ₐ[O] G.A n) c`. Rewrite using `[endo_apply, endo_apply, map_sum]`. Repeatedly rewrite using `[map_smul, hp, Finset.smul_sum, smul_ite, smul_zero]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c' _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_univ, if_true]`. Rewrite using `[sig_res hw]`. Both sides reduce to the same expression.
-/
theorem res_endo (H : HasIdem O) (n : ℕ) (a : G.A (n + 1)) :
    G.res n (endo s hpt he (n + 1) a) = endo s hpt he n (G.res n a) := by
  have hp : ∀ c, G.res n (e (n + 1) c) = ∑ c', if c'.comp (G.res n : G.A (n + 1) →ₐ[O] G.A n) = c
      then e n c' else 0 := fun c => by
    exact push_e H (he (n + 1)) (he n) (G.res n : G.A (n + 1) →ₐ[O] G.A n) c
  rw [endo_apply, endo_apply, map_sum]
  simp_rw [map_smul, hp, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, if_true]
  rw [sig_res hw]
  rfl

variable (s hpt) in
include hpt he in

def uEnd (H : HasIdem O) : G ⟶ G where
  app n := BialgHom.ofAlgHom (endo s hpt he n) (counit_endo hs hw he n) (comul_endo hw he H n)
  comm n := BialgHom.ext fun a => res_endo hw he H n a

include hs hw hpt in
/- English proof (translation)
Introduce `f g h` and use `funext fun c => by have h1 := congrArg (sig G s hpt n c) h rwa [sig_sumE hs hw he, sig_sumE hs hw he] at h1`.
-/
theorem sumE_injective (n : ℕ) : Function.Injective (sumE (he n)) := fun f g h =>
  funext fun c => by
    have h1 := congrArg (sig G s hpt n c) h
    rwa [sig_sumE hs hw he, sig_sumE hs hw he] at h1

include hs hw in
/- English proof (translation)
Use `le_antisymm (AlgHom.range_comp_le_range _ _) ?_` and prove the remaining obligations. Introduce and unpack `x ⟨f, rfl⟩`. Conclude with `⟨sumE (he n) f, endo_sumE hs hw he n f⟩`.
-/
theorem range_endo (n : ℕ) : (endo s hpt he n).range = (sumE (he n)).range := by
  refine le_antisymm (AlgHom.range_comp_le_range _ _) ?_
  rintro x ⟨f, rfl⟩
  exact ⟨sumE (he n) f, endo_sumE hs hw he n f⟩

include hs hw hpt he in
/- English proof (translation)
Use `⟨uEnd s hpt hs hw he H, hom_ext fun n => BialgHom.ext fun a => endo_endo hs hw he n a, fun n c a => ?_, fun n => ⟨Fintype.card (G.A n →ₐ[O] IsLocalRing.ResidueField O), ⟨?_⟩⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `c (endo s hpt he n a) = c a`. Rewrite using `[endo_apply, map_sum]`. Repeatedly rewrite using `[map_smul, (he n).pt, smul_ite, smul_zero]`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using `only [Finset.mem_univ, if_true, Algebra.smul_def, mul_one]`. Conclude with `DFunLike.congr_fun (ofId_comp_sig (hpt := hpt) hs hw n c) a`. Establish `h : ((uEnd s hpt hs hw he H).app n : G.A n →ₐ[O] G.A n) = endo s hpt he n` using `rfl`. Rewrite using `[h]`. Conclude with `((Subalgebra.equivOfEq _ _ (range_endo hs hw he n)).trans (AlgEquiv.ofInjective _ (sumE_injective (hpt := hpt) hs hw he n)).symm).trans (AlgEquiv.piCongrLeft O (fun _ => O) (Fintype.equivFin _).symm).symm`.
-/
theorem exists_endo (H : HasIdem O) : ∃ u : G ⟶ G, u ≫ u = u ∧
    (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) (a : G.A n), c (u.app n a) = c a) ∧
    ∀ n, ∃ N : ℕ, Nonempty ((u.app n : G.A n →ₐ[O] G.A n).range ≃ₐ[O] (Fin N → O)) := by
  refine ⟨uEnd s hpt hs hw he H, hom_ext fun n => BialgHom.ext fun a => endo_endo hs hw he n a,
    fun n c a => ?_, fun n => ⟨Fintype.card (G.A n →ₐ[O] IsLocalRing.ResidueField O), ⟨?_⟩⟩⟩
  · change c (endo s hpt he n a) = c a
    rw [endo_apply, map_sum]
    simp_rw [map_smul, (he n).pt, smul_ite, smul_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, Algebra.smul_def, mul_one]
    exact DFunLike.congr_fun (ofId_comp_sig (hpt := hpt) hs hw n c) a
  · have h : ((uEnd s hpt hs hw he H).app n : G.A n →ₐ[O] G.A n) = endo s hpt he n := rfl
    rw [h]
    exact ((Subalgebra.equivOfEq _ _ (range_endo hs hw he n)).trans
      (AlgEquiv.ofInjective _ (sumE_injective (hpt := hpt) hs hw he n)).symm).trans
      (AlgEquiv.piCongrLeft O (fun _ => O) (Fintype.equivFin _).symm).symm

end Endo2

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ hv G`. Establish `H : HasIdem O` using `fun A _ _ _ => GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC p C v O hv A`. Take `⟨hpt, s, hs, hw⟩` from `GlobalTheory.T.pDivGroup_residueField_tate_level_section p C v O hv G`. Establish `hH : ∀ n, Finite (G.A n →ₐ[O] IsLocalRing.ResidueField O) ∧ ∃ e, IdemData (G.A n) e` using `fun n => H (G.A n)`. Use `choose hfin e he using hH`.

Use `haveI : ∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O) := fun n => Fintype.ofFinite _`. Conclude with `exists_endo (hpt := hpt) hs hw he H`.
-/
theorem exists_idempotent_constPart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ G : PDivGroup p O, ∃ u : G ⟶ G, u ≫ u = u ∧ (∀ (n : ℕ) (c : G.A n →ₐ[O] IsLocalRing.ResidueField O) (a : G.A n), c (u.app n a) = c a) ∧ ∀ n, ∃ N : ℕ, Nonempty ((u.app n : G.A n →ₐ[O] G.A n).range ≃ₐ[O] (Fin N → O)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ hv G
  have H : HasIdem O := fun A _ _ _ => GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC p C v O hv A
  obtain ⟨hpt, s, hs, hw⟩ := GlobalTheory.T.pDivGroup_residueField_tate_level_section p C v O hv G
  have hH : ∀ n, Finite (G.A n →ₐ[O] IsLocalRing.ResidueField O) ∧
      ∃ e, IdemData (G.A n) e := fun n => H (G.A n)
  choose hfin e he using hH
  haveI : ∀ n, Fintype (G.A n →ₐ[O] IsLocalRing.ResidueField O) := fun n => Fintype.ofFinite _
  exact exists_endo (hpt := hpt) hs hw he H

end GlobalTheory.ConstPart
