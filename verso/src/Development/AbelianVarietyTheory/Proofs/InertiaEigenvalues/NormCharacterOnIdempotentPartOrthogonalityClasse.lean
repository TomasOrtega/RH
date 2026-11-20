import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCharacterOnIdempotentPartFramePropertiesStatement

noncomputable section

namespace GlobalTheory.UnitLemma.Desc

open GlobalTheory.UnitLemma Polynomial Filter Topology

/- English proof (translation)
Establish `h1 : ∀ I : Finset ι, (-1 : ℝ) ^ (J ∩ I).card = ∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1)`. Introduce `I`. Rewrite using `[Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter, Finset.inter_comm]`. Establish `h2 : ∑ I ∈ S.powerset, (∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1)) = ∏ i ∈ S, ((if i ∈ J then (-1 : ℝ) else 1) + 1)`. Rewrite using `[Finset.prod_add]`.

Simplify using the standard rewrite rules. Repeatedly rewrite using `[h1]`. Rewrite using `[h2]`. Use `split_ifs with hJe`. Substitute `hJe` using the available equality.

Simplify using `only [Finset.notMem_empty, if_false, Finset.prod_const]`. Evaluate the numerical expressions. Take `⟨j, hj⟩` from `Finset.nonempty_iff_ne_empty.2 hJe`. Conclude with `Finset.prod_eq_zero (hJ hj) (by simp [hj])`.
-/
theorem sum_powerset_neg_one_pow_inter {ι : Type} [DecidableEq ι] (S J : Finset ι) (hJ : J ⊆ S) :
    ∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card = if J = ∅ then 2 ^ S.card else 0 := by
  have h1 : ∀ I : Finset ι, (-1 : ℝ) ^ (J ∩ I).card = ∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1) := by
    intro I
    rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.inter_comm]
  have h2 : ∑ I ∈ S.powerset, (∏ i ∈ I, (if i ∈ J then (-1 : ℝ) else 1)) =
      ∏ i ∈ S, ((if i ∈ J then (-1 : ℝ) else 1) + 1) := by
    rw [Finset.prod_add]
    simp
  simp_rw [h1]
  rw [h2]
  split_ifs with hJe
  · subst hJe
    simp only [Finset.notMem_empty, if_false, Finset.prod_const]
    norm_num
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.2 hJe
    exact Finset.prod_eq_zero (hJ hj) (by simp [hj])

/- English proof (translation)
Use `⟨Quot.lift (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => chi B e I (x.1 : B.A)) ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `x y ⟨u, hu⟩`. Rewrite using `[hu, hmul _ _ x.1.isUnit (u.isUnit.mul (u.isUnit.map B.σ)), hnorm _ u.isUnit, mul_one]`. Introduce `k conv_lhs => rw [← Quot.out_eq k]`. Both sides reduce to the same expression.

Introduce `x`. Both sides reduce to the same expression.
-/
theorem chi_cl_lift {K : UQ} (B : InvAlg K) {ι : Type} (e : ι → B.A) (I : Finset ι)
    (hmul : ∀ x y : B.A, IsUnit x → IsUnit y → chi B e I (x * y) = chi B e I x * chi B e I y)
    (hnorm : ∀ w : B.A, IsUnit w → chi B e I (w * B.σ w) = 1) :
    ∃ F : B.Cl → ℚ, (∀ k, F k = chi B e I k.rep) ∧
      ∀ x : {x : B.Aˣ // B.σ (x : B.A) = x}, F (Quot.mk _ x) = chi B e I (x.1 : B.A) := by
  refine ⟨Quot.lift (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => chi B e I (x.1 : B.A)) ?_, ?_, ?_⟩
  · rintro x y ⟨u, hu⟩
    rw [hu, hmul _ _ x.1.isUnit (u.isUnit.mul (u.isUnit.map B.σ)), hnorm _ u.isUnit, mul_one]
  · intro k
    conv_lhs => rw [← Quot.out_eq k]
    rfl
  · intro x; rfl

/- English proof (translation)
Take `⟨hmul, hnorm, hpi, -⟩` from `GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B ι e π S hF`. Use `split_ifs with hII`. Substitute `hII` using the available equality. Establish `: ∀ k : B.Cl, chi B e I k.rep * chi B e I k.rep = 1` using `fun k => eta_sq _`. Simplify using `[this]`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hjS, hj⟩ : ∃ j ∈ S, ¬ (j ∈ I ↔ j ∈ I₀) := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `hII` to reduce the goal to its premises. Use extensionality with `j`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(hc j (hI h)).1 h`. Introduce `h`. Conclude with `(hc j (h₀ h)).2 h`.

Establish `hp : B.Plus (π j)` using `(hF.2 j hjS).1`. Use `set v : B.Aˣ := hp.1.unit with hvdef`. Establish `hvv : (v : B.A) = π j` using `hp.1.unit_spec`. Establish `hv : B.σ (v : B.A) = v` using `by rw [hvv]; exact hp.2`. Establish `hv' : B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, Units.inv_mul, one_mul]`. Use `_ = ((v⁻¹ : B.Aˣ) : B.A) := by`. Rewrite using `[← hv, ← map_mul, Units.mul_inv, map_one, mul_one]`. Establish `hsign : chi B e I₀ (π j) * chi B e I (π j) = -1`.

Establish `a0` using `hpi I₀ {j} h₀ (Finset.singleton_subset_iff.2 hjS)`. Establish `a1` using `hpi I {j} hI (Finset.singleton_subset_iff.2 hjS)`. Rewrite `a0`, `a1` using `[Finset.prod_singleton]`. Rewrite using `[a0, a1]`. Distinguish the cases in `hjI : j ∈ I`.

Establish `hjI0 : j ∉ I₀` using `fun h => hj ⟨fun _ => h, fun _ => hjI⟩`. Simplify using `[Finset.singleton_inter_of_mem hjI, Finset.singleton_inter_of_notMem hjI0]`. Establish `hjI0 : j ∈ I₀` using `by by_contra h; exact hj ⟨fun h' => absurd h' hjI, fun h' => absurd h' h⟩`. Simplify using `[Finset.singleton_inter_of_mem hjI0, Finset.singleton_inter_of_notMem hjI]`. Take `⟨F₀, hF₀, hF₀mk⟩` from `chi_cl_lift B e I₀ (hmul I₀) (hnorm I₀)`.

Take `⟨F₁, hF₁, hF₁mk⟩` from `chi_cl_lift B e I (hmul I) (hnorm I)`. Set `T : B.Cl → B.Cl` to `Quot.map (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => (⟨v * x.1, by rw [Units.val_mul, map_mul, hv, x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x})) (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)`. Set `T' : B.Cl → B.Cl` to `Quot.map (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} => (⟨v⁻¹ * x.1, by rw [Units.val_mul, map_mul, hv', x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x})) (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)`. Set `E : B.Cl ≃ B.Cl` to `{ toFun := T, invFun := T' left_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (inv_mul_cancel_left v x.1)) right_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (mul_inv_cancel_left v x.1)) }`. Establish `key : ∀ k, F₀ (E k) * F₁ (E k) = -(F₀ k * F₁ k)`.

Introduce `k`. Proceed by induction on `k using Quot.ind with`. Consider the case `mk x`. Express the relevant statement in the definitionally equal form `F₀ (Quot.mk _ _) * F₁ (Quot.mk _ _) = _`. Rewrite using `[hF₀mk, hF₀mk, hF₁mk, hF₁mk, Units.val_mul, hmul I₀ _ _ v.isUnit x.1.isUnit, hmul I _ _ v.isUnit x.1.isUnit, hvv]`.

Take the linear combination `(chi B e I₀ (x.1 : B.A) * chi B e I (x.1 : B.A)) * hsign`. Establish `hs : ∑ k : B.Cl, F₀ k * F₁ k = 0`. Use `Equiv.sum_comp E (fun k => F₀ k * F₁ k)` as an intermediate fact. Simplify using `only [key, Finset.sum_neg_distrib] at this`. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify `hs` using `[hF₀, hF₁]`.
-/
theorem sum_chi_mul_chi {K : UQ} (B : InvAlg K) {ι : Type} [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι) (hF : IsFrame B e π S) [Fintype B.Cl] (I₀ I : Finset ι) (h₀ : I₀ ⊆ S) (hI : I ⊆ S) :
    ∑ k : B.Cl, chi B e I₀ k.rep * chi B e I k.rep = if I = I₀ then (Fintype.card B.Cl : ℚ) else 0 := by
  obtain ⟨hmul, hnorm, hpi, -⟩ := GlobalTheory.T.normCharacterOnIdempotentPart_frame_properties K B ι e π S hF
  split_ifs with hII
  · subst hII
    have : ∀ k : B.Cl, chi B e I k.rep * chi B e I k.rep = 1 := fun k => eta_sq _
    simp [this]
  · obtain ⟨j, hjS, hj⟩ : ∃ j ∈ S, ¬ (j ∈ I ↔ j ∈ I₀) := by
      by_contra hc
      push_neg at hc
      apply hII
      ext j
      constructor
      · intro h; exact (hc j (hI h)).1 h
      · intro h; exact (hc j (h₀ h)).2 h
    have hp : B.Plus (π j) := (hF.2 j hjS).1
    set v : B.Aˣ := hp.1.unit with hvdef
    have hvv : (v : B.A) = π j := hp.1.unit_spec
    have hv : B.σ (v : B.A) = v := by rw [hvv]; exact hp.2
    have hv' : B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) := by
      calc B.σ ((v⁻¹ : B.Aˣ) : B.A) = ((v⁻¹ : B.Aˣ) : B.A) * ((v : B.A) * B.σ ((v⁻¹ : B.Aˣ) : B.A)) := by
            rw [← mul_assoc, Units.inv_mul, one_mul]
        _ = ((v⁻¹ : B.Aˣ) : B.A) := by
            rw [← hv, ← map_mul, Units.mul_inv, map_one, mul_one]
    have hsign : chi B e I₀ (π j) * chi B e I (π j) = -1 := by
      have a0 := hpi I₀ {j} h₀ (Finset.singleton_subset_iff.2 hjS)
      have a1 := hpi I {j} hI (Finset.singleton_subset_iff.2 hjS)
      rw [Finset.prod_singleton] at a0 a1
      rw [a0, a1]
      by_cases hjI : j ∈ I
      · have hjI0 : j ∉ I₀ := fun h => hj ⟨fun _ => h, fun _ => hjI⟩
        simp [Finset.singleton_inter_of_mem hjI, Finset.singleton_inter_of_notMem hjI0]
      · have hjI0 : j ∈ I₀ := by by_contra h; exact hj ⟨fun h' => absurd h' hjI, fun h' => absurd h' h⟩
        simp [Finset.singleton_inter_of_mem hjI0, Finset.singleton_inter_of_notMem hjI]
    obtain ⟨F₀, hF₀, hF₀mk⟩ := chi_cl_lift B e I₀ (hmul I₀) (hnorm I₀)
    obtain ⟨F₁, hF₁, hF₁mk⟩ := chi_cl_lift B e I (hmul I) (hnorm I)
    let T : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v * x.1, by rw [Units.val_mul, map_mul, hv, x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let T' : B.Cl → B.Cl := Quot.map
      (fun x : {x : B.Aˣ // B.σ (x : B.A) = x} =>
        (⟨v⁻¹ * x.1, by rw [Units.val_mul, map_mul, hv', x.2]⟩ : {x : B.Aˣ // B.σ (x : B.A) = x}))
      (by rintro x y ⟨u, hu⟩; exact ⟨u, by simp only [Units.val_mul]; rw [hu, mul_assoc]⟩)
    let E : B.Cl ≃ B.Cl :=
      { toFun := T, invFun := T'
        left_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (inv_mul_cancel_left v x.1))
        right_inv := fun k => Quot.inductionOn k fun x => congrArg (Quot.mk _) (Subtype.ext (mul_inv_cancel_left v x.1)) }
    have key : ∀ k, F₀ (E k) * F₁ (E k) = -(F₀ k * F₁ k) := by
      intro k
      induction k using Quot.ind with
      | mk x =>
        change F₀ (Quot.mk _ _) * F₁ (Quot.mk _ _) = _
        rw [hF₀mk, hF₀mk, hF₁mk, hF₁mk, Units.val_mul, hmul I₀ _ _ v.isUnit x.1.isUnit,
          hmul I _ _ v.isUnit x.1.isUnit, hvv]
        linear_combination (chi B e I₀ (x.1 : B.A) * chi B e I (x.1 : B.A)) * hsign
    have hs : ∑ k : B.Cl, F₀ k * F₁ k = 0 := by
      have := Equiv.sum_comp E (fun k => F₀ k * F₁ k)
      simp only [key, Finset.sum_neg_distrib] at this
      linarith
    simpa [hF₀, hF₁] using hs

/- English proof (translation)
Introduce `K B ι _ _ e π S hF hfin ℓ h hyp I₀ h₀`. Use `haveI := Fintype.ofFinite B.Cl`. Establish `inv : ∀ x, B.Plus x → (2 : ℝ) ^ S.card * ℓ x = ∑ I ∈ S.powerset, (chi B e I x : ℝ) * h I`. Introduce `x hx`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.sum_eq_single ∅]`. Simplify using `[sum_powerset_neg_one_pow_inter S ∅ (Finset.empty_subset _)]`. Introduce `J hJ hJe`. Rewrite using `[sum_powerset_neg_one_pow_inter S J (Finset.mem_powerset.1 hJ), if_neg hJe, zero_mul]`. Introduce `hn`.

Conclude with `absurd (Finset.empty_mem_powerset S) hn`. Use `_ = ∑ I ∈ S.powerset, ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) := by`. Repeatedly rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_comm`. Use `_ = _ := Finset.sum_congr rfl fun I hI => hyp I (Finset.mem_powerset.1 hI) x hx`.

Establish `hplus : ∀ k : B.Cl, B.Plus k.rep` using `fun k => ⟨(Quot.out k).1.isUnit, (Quot.out k).2⟩`. Establish `e1 : ∀ k : B.Cl, ℓ k.rep = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I`. Introduce `k; rw [← inv _ (hplus k), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]`. Establish `orth : ∀ I ∈ S.powerset, ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) = if I = I₀ then (Fintype.card B.Cl : ℝ) else 0`. Introduce `I hI`.

Use `sum_chi_mul_chi B e π S hF I₀ I h₀ (Finset.mem_powerset.1 hI)` as an intermediate fact. Apply the tactic sequence `split_ifs at this ⊢ <;> exact_mod_cast this`. Rewrite using `[finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]`. Repeatedly rewrite using `[e1]`. Combine the equalities or inequalities in the displayed calculation.

Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun k _ => by ring`. Use `_ = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * (if I = I₀ then (Fintype.card B.Cl : ℝ) else 0) := by`. Rewrite using `[Finset.sum_congr rfl fun I hI => by rw [orth I hI]]`.

Use `_ = (Fintype.card B.Cl : ℝ) / 2 ^ S.card * h I₀ := by`. Simplify using `only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_powerset.2 h₀, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_chi_ell_cl : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] [DecidableEq ι] (e π : ι → B.A)
    (S : Finset ι), IsFrame B e π S → Finite B.Cl → ∀ (ℓ : B.A → ℝ) (h : Finset ι → ℝ),
    (∀ I ⊆ S, ∀ x, B.Plus x → ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) =
      (chi B e I x : ℝ) * h I) →
    ∀ I ⊆ S, ∑ᶠ k : B.Cl, (chi B e I k.rep : ℝ) * ℓ k.rep = (Nat.card B.Cl : ℝ) / 2 ^ S.card * h I := by
  intro K B ι _ _ e π S hF hfin ℓ h hyp I₀ h₀
  haveI := Fintype.ofFinite B.Cl
  have inv : ∀ x, B.Plus x → (2 : ℝ) ^ S.card * ℓ x = ∑ I ∈ S.powerset, (chi B e I x : ℝ) * h I := by
    intro x hx
    calc (2 : ℝ) ^ S.card * ℓ x
        = ∑ J ∈ S.powerset, (∑ I ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card) * ℓ ((∏ j ∈ J, π j) * x) := by
          rw [Finset.sum_eq_single ∅]
          · simp [sum_powerset_neg_one_pow_inter S ∅ (Finset.empty_subset _)]
          · intro J hJ hJe
            rw [sum_powerset_neg_one_pow_inter S J (Finset.mem_powerset.1 hJ), if_neg hJe, zero_mul]
          · intro hn; exact absurd (Finset.empty_mem_powerset S) hn
      _ = ∑ I ∈ S.powerset, ∑ J ∈ S.powerset, (-1 : ℝ) ^ (J ∩ I).card * ℓ ((∏ j ∈ J, π j) * x) := by
          simp_rw [Finset.sum_mul]; exact Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun I hI => hyp I (Finset.mem_powerset.1 hI) x hx
  have hplus : ∀ k : B.Cl, B.Plus k.rep := fun k => ⟨(Quot.out k).1.isUnit, (Quot.out k).2⟩
  have e1 : ∀ k : B.Cl, ℓ k.rep = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I := by
    intro k; rw [← inv _ (hplus k), ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have orth : ∀ I ∈ S.powerset, ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) =
      if I = I₀ then (Fintype.card B.Cl : ℝ) else 0 := by
    intro I hI
    have := sum_chi_mul_chi B e π S hF I₀ I h₀ (Finset.mem_powerset.1 hI)
    split_ifs at this ⊢ <;> exact_mod_cast this
  rw [finsum_eq_sum_of_fintype, Nat.card_eq_fintype_card]
  simp_rw [e1]
  calc ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, (chi B e I k.rep : ℝ) * h I)
      = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * ∑ k : B.Cl, (chi B e I₀ k.rep : ℝ) * (chi B e I k.rep : ℝ) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun k _ => by ring
    _ = ((2 : ℝ) ^ S.card)⁻¹ * ∑ I ∈ S.powerset, h I * (if I = I₀ then (Fintype.card B.Cl : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun I hI => by rw [orth I hI]]
    _ = (Fintype.card B.Cl : ℝ) / 2 ^ S.card * h I₀ := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_powerset.2 h₀, if_true]
        ring

end GlobalTheory.UnitLemma.Desc
