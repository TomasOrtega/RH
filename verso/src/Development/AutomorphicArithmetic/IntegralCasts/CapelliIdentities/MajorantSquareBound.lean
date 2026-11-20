import Mathlib

open Polynomial Finset MvPolynomial in
/- English proof (translation)
Use `set n := Fintype.card σ with hn`. Set `P : (MvPolynomial σ ℤ)[X]` to `∏ I ∈ Finset.powersetCard r (Finset.univ : Finset σ), (Polynomial.X - Polynomial.C (∏ i ∈ I, (MvPolynomial.X i : MvPolynomial σ ℤ)))`. Establish `hsym : ∀ j, (P.coeff j).IsSymmetric`. Introduce `j e`. Establish `h1 : P.map (MvPolynomial.rename e).toRingHom = P`.

Simplify using `only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Use `Finset.prod_bij' (fun I _ => I.map e.toEmbedding) (fun I _ => I.map e.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `I hI`. Simplify `hI` using `[Finset.mem_powersetCard]`. Introduce `I hI`.

Simplify `hI` using `[Finset.mem_powersetCard]`. Introduce `I _`. Use `ext`. Simplify using the standard rewrite rules. Introduce `I _`.

Use `ext`. Simplify using the standard rewrite rules. Introduce `I _`. Simplify using `[map_prod]`. Use `congrArg (fun p => p.coeff j) h1` as an intermediate fact.

Simplify `this` using `[Polynomial.coeff_map]`. Set `f : MvPolynomial (Fin n) ℤ →+* MvPolynomial σ ℤ` to `(MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm σ ℤ (i + 1))).toRingHom`. Establish `hP : P ∈ Polynomial.lifts f`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `j`.

Take `⟨E, hE⟩` from `MvPolynomial.esymmAlgHom_surjective ℤ (σ := σ) (n := n) le_rfl ⟨P.coeff j, hsym j⟩`. Use `⟨E, ?_⟩` and prove the remaining obligations. Use `congrArg Subtype.val hE` as an intermediate fact. Simplify `this` using `[MvPolynomial.esymmAlgHom_apply, f]`. Take `⟨P', hP'⟩` from `hP`.

Set `e : Fin n → B` to `fun k => (-1) ^ ((k : ℕ) + 1) * Q.coeff (n - ((k : ℕ) + 1))`. Set `Θ : MvPolynomial (Fin n) ℤ →+* B` to `(MvPolynomial.aeval e).toRingHom`. Use `⟨P'.map Θ, ?_⟩` and prove the remaining obligations. Introduce `R _ φ θ hQ`. Establish `hcomp : φ.comp Θ = ((MvPolynomial.aeval θ : MvPolynomial σ ℤ →ₐ[ℤ] R).toRingHom).comp f`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[Θ, f]`. Introduce `i`. Establish `hi : (i : ℕ) + 1 ≤ n` using `i.2`.

Establish `hs : Multiset.card ((Finset.univ : Finset σ).val.map θ) = n` using `by simp [hn]`. Establish `h1 : (Q.map φ).coeff (n - ((i : ℕ) + 1)) = (-1) ^ ((i : ℕ) + 1) * ((Finset.univ : Finset σ).val.map θ).esymm ((i : ℕ) + 1)`. Establish `h2 : Q.map φ = (((Finset.univ : Finset σ).val.map θ).map (fun t => Polynomial.X - Polynomial.C t)).prod`. Rewrite using `[hQ, Multiset.map_map]`. Both sides reduce to the same expression.

Rewrite using `[h2, Multiset.prod_X_sub_C_coeff _ (by rw [hs]; omega), hs]`. Establish `: n - (n - ((i : ℕ) + 1)) = (i : ℕ) + 1` using `by omega`. Rewrite using `[this]`. Establish `h3 : φ (Q.coeff (n - ((i : ℕ) + 1))) = (Q.map φ).coeff (n - ((i : ℕ) + 1))`. Rewrite using `[Polynomial.coeff_map]`.

Simplify using `only [RingHom.comp_apply, Θ, f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, e, map_mul, map_pow, map_neg, map_one]`. Rewrite using `[h3, h1, MvPolynomial.aeval_esymm_eq_multiset_esymm, ← mul_assoc, ← mul_pow]`. Simplify using the standard rewrite rules. Establish `hP'' : P'.map f = P` using `hP'`. Rewrite using `[Polynomial.map_map, hcomp, ← Polynomial.map_map, hP'']`.

Simplify using `only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]`. Simplify using the standard rewrite rules.
-/
private theorem exF {B : Type} [CommRing B] (σ : Type) [Fintype σ] [DecidableEq σ] (Q : B[X]) (r : ℕ) :
    ∃ F : B[X], ∀ (R : Type) [CommRing R] (φ : B →+* R) (θ : σ → R),
      Q.map φ = ∏ i, (Polynomial.X - Polynomial.C (θ i)) →
      F.map φ = ∏ I ∈ Finset.powersetCard r (Finset.univ : Finset σ),
        (Polynomial.X - Polynomial.C (∏ i ∈ I, θ i)) := by
  classical
  set n := Fintype.card σ with hn
  let P : (MvPolynomial σ ℤ)[X] := ∏ I ∈ Finset.powersetCard r (Finset.univ : Finset σ),
        (Polynomial.X - Polynomial.C (∏ i ∈ I, (MvPolynomial.X i : MvPolynomial σ ℤ)))
  have hsym : ∀ j, (P.coeff j).IsSymmetric := by
    intro j e
    have h1 : P.map (MvPolynomial.rename e).toRingHom = P := by
      simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      refine Finset.prod_bij' (fun I _ => I.map e.toEmbedding) (fun I _ => I.map e.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_
      · intro I hI; simpa [Finset.mem_powersetCard] using hI
      · intro I hI; simpa [Finset.mem_powersetCard] using hI
      · intro I _; ext; simp
      · intro I _; ext; simp
      · intro I _; simp [map_prod]
    have := congrArg (fun p => p.coeff j) h1
    simpa [Polynomial.coeff_map] using this
  let f : MvPolynomial (Fin n) ℤ →+* MvPolynomial σ ℤ :=
    (MvPolynomial.aeval (fun i : Fin n => MvPolynomial.esymm σ ℤ (i + 1))).toRingHom
  have hP : P ∈ Polynomial.lifts f := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro j
    obtain ⟨E, hE⟩ := MvPolynomial.esymmAlgHom_surjective ℤ  (σ := σ) (n := n) le_rfl ⟨P.coeff j, hsym j⟩
    refine ⟨E, ?_⟩
    have := congrArg Subtype.val hE
    simpa [MvPolynomial.esymmAlgHom_apply, f] using this
  obtain ⟨P', hP'⟩ := hP
  let e : Fin n → B := fun k => (-1) ^ ((k : ℕ) + 1) * Q.coeff (n - ((k : ℕ) + 1))
  let Θ : MvPolynomial (Fin n) ℤ →+* B := (MvPolynomial.aeval e).toRingHom
  refine ⟨P'.map Θ, ?_⟩
  intro R _ φ θ hQ
  have hcomp : φ.comp Θ = ((MvPolynomial.aeval θ : MvPolynomial σ ℤ →ₐ[ℤ] R).toRingHom).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [Θ, f]
    · intro i
      have hi : (i : ℕ) + 1 ≤ n := i.2
      have hs : Multiset.card ((Finset.univ : Finset σ).val.map θ) = n := by simp [hn]
      have h1 : (Q.map φ).coeff (n - ((i : ℕ) + 1)) =
          (-1) ^ ((i : ℕ) + 1) * ((Finset.univ : Finset σ).val.map θ).esymm ((i : ℕ) + 1) := by
        have h2 : Q.map φ = (((Finset.univ : Finset σ).val.map θ).map
            (fun t => Polynomial.X - Polynomial.C t)).prod := by
          rw [hQ, Multiset.map_map]; rfl
        rw [h2, Multiset.prod_X_sub_C_coeff _ (by rw [hs]; omega), hs]
        have : n - (n - ((i : ℕ) + 1)) = (i : ℕ) + 1 := by omega
        rw [this]
      have h3 : φ (Q.coeff (n - ((i : ℕ) + 1))) = (Q.map φ).coeff (n - ((i : ℕ) + 1)) := by
        rw [Polynomial.coeff_map]
      simp only [RingHom.comp_apply, Θ, f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, e, map_mul, map_pow, map_neg, map_one]
      rw [h3, h1, MvPolynomial.aeval_esymm_eq_multiset_esymm, ← mul_assoc, ← mul_pow]
      simp
  have hP'' : P'.map f = P := hP'
  rw [Polynomial.map_map, hcomp, ← Polynomial.map_map, hP'']
  simp only [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  simp

open Classical in
/- English proof (translation)
Establish `h2 : q.map ι = (((Finset.univ : Finset σ).val.map θ).map (fun t => Polynomial.X - Polynomial.C t)).prod`. Rewrite using `[h, Multiset.map_map]`. Both sides reduce to the same expression. Establish `h3 : q.rootMultiplicity 0 = (q.map ι).rootMultiplicity (ι 0)` using `Polynomial.eq_rootMultiplicity_map ι.injective 0`. Rewrite using `[h3, map_zero, ← Polynomial.count_roots, h2, Polynomial.roots_multiset_prod_X_sub_C, Multiset.count_map]`.

Simplify using `only [Finset.card_def, Finset.filter_val]`. Use `congr 1`. Conclude with `Multiset.filter_congr (fun i _ => eq_comm)`.
-/
private theorem card_zero {k L : Type} [Field k] [Field L] (ι : k →+* L) {σ : Type} [Fintype σ] [DecidableEq σ]
    (q : Polynomial k) (θ : σ → L)
    (h : q.map ι = ∏ i, (Polynomial.X - Polynomial.C (θ i))) :
    (Finset.univ.filter (fun i => θ i = 0)).card = q.rootMultiplicity 0 := by
  classical
  have h2 : q.map ι = (((Finset.univ : Finset σ).val.map θ).map
      (fun t => Polynomial.X - Polynomial.C t)).prod := by
    rw [h, Multiset.map_map]; rfl
  have h3 : q.rootMultiplicity 0 = (q.map ι).rootMultiplicity (ι 0) :=
    Polynomial.eq_rootMultiplicity_map ι.injective 0
  rw [h3, map_zero, ← Polynomial.count_roots, h2, Polynomial.roots_multiset_prod_X_sub_C,
    Multiset.count_map]
  simp only [Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr (fun i _ => eq_comm)

open Classical in
/- English proof (translation)
Rewrite using `[← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => θ i = 0)]`. Establish `h1 : ∏ i ∈ Finset.univ.filter (fun i => θ i = 0), (Polynomial.X - Polynomial.C (θ i)) = (Polynomial.X : Polynomial L) ^ (Finset.univ.filter (fun i => θ i = 0)).card`. Rewrite using `[Finset.prod_congr rfl (g := fun _ => (Polynomial.X : Polynomial L))]`. Simplify using the standard rewrite rules. Introduce `i hi`.

Simplify using `[(Finset.mem_filter.mp hi).2]`. Rewrite using `[h1]`. Use `Polynomial.coeff_X_pow_mul (∏ i ∈ Finset.univ.filter (fun i => ¬ θ i = 0), (Polynomial.X - Polynomial.C (θ i))) (Finset.univ.filter (fun i => θ i = 0)).card 0` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]`.

Simplify using `[Finset.prod_neg]`.
-/
private theorem coeff_mid {L : Type} [Field L] {σ : Type} [Fintype σ] [DecidableEq σ] (θ : σ → L) :
    (∏ i, (Polynomial.X - Polynomial.C (θ i))).coeff (Finset.univ.filter (fun i => θ i = 0)).card =
      (-1) ^ (Finset.univ.filter (fun i => ¬ θ i = 0)).card *
        ∏ i ∈ Finset.univ.filter (fun i => ¬ θ i = 0), θ i := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => θ i = 0)]
  have h1 : ∏ i ∈ Finset.univ.filter (fun i => θ i = 0), (Polynomial.X - Polynomial.C (θ i))
      = (Polynomial.X : Polynomial L) ^ (Finset.univ.filter (fun i => θ i = 0)).card := by
    rw [Finset.prod_congr rfl (g := fun _ => (Polynomial.X : Polynomial L))]
    · simp
    · intro i hi
      simp [(Finset.mem_filter.mp hi).2]
  rw [h1]
  have := Polynomial.coeff_X_pow_mul (∏ i ∈ Finset.univ.filter (fun i => ¬ θ i = 0), (Polynomial.X - Polynomial.C (θ i))) (Finset.univ.filter (fun i => θ i = 0)).card 0
  rw [zero_add] at this
  rw [this, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  simp [Finset.prod_neg]

/- English proof (translation)
Set `ι : IsLocalRing.ResidueField B →+* L` to `Ideal.Quotient.lift (IsLocalRing.maximalIdeal B) ψ (fun b hb => (hker b).2 hb)`. Establish `hι : ι.comp (IsLocalRing.residue B) = ψ`. Use extensionality with `b`. Both sides reduce to the same expression. Establish `h2 : (Q.map (IsLocalRing.residue B)).map ι = ∏ i, (Polynomial.X - Polynomial.C (θ i))`.

Rewrite using `[Polynomial.map_map, hι, h]`. Use `card_zero ι _ θ h2` and compare the differences between its conclusion and the goal.
-/
private theorem data {B : Type} [CommRing B] [IsLocalRing B] {L : Type} [Field L] (ψ : B →+* L)
    (hker : ∀ b, ψ b = 0 ↔ b ∈ IsLocalRing.maximalIdeal B) (Q : Polynomial B)
    {σ : Type} [Fintype σ] [DecidableEq σ] (θ : σ → L)
    (h : Q.map ψ = ∏ i, (Polynomial.X - Polynomial.C (θ i))) [DecidablePred fun i => θ i = 0] :
    (Finset.univ.filter (fun i => θ i = 0)).card =
      (Q.map (IsLocalRing.residue B)).rootMultiplicity 0 := by
  let ι : IsLocalRing.ResidueField B →+* L :=
    Ideal.Quotient.lift (IsLocalRing.maximalIdeal B) ψ (fun b hb => (hker b).2 hb)
  have hι : ι.comp (IsLocalRing.residue B) = ψ := by
    ext b; rfl
  have h2 : (Q.map (IsLocalRing.residue B)).map ι = ∏ i, (Polynomial.X - Polynomial.C (θ i)) := by
    rw [Polynomial.map_map, hι, h]
  convert card_zero ι _ θ h2

/- English proof (translation)
Establish `hcomap : ∀ n : Ideal S, n.IsMaximal → n.comap (algebraMap B S) = IsLocalRing.maximalIdeal B`. Introduce `n hn`. Use `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) n` as an intermediate fact. Conclude with `IsLocalRing.eq_maximalIdeal this`. Establish `hkerI : ∀ n : Ideal S, n.IsMaximal → ∀ b, algebraMap B S b ∈ n ↔ b ∈ IsLocalRing.maximalIdeal B`.

Introduce `n hn b`. Rewrite using `[← hcomap n hn, Ideal.mem_comap]`. Use `set a := (Q.map (IsLocalRing.residue B)).rootMultiplicity 0 with ha`. Establish `hmapn : ∀ n : Ideal S, Q.map ((Ideal.Quotient.mk n).comp (algebraMap B S)) = ∏ i, (Polynomial.X - Polynomial.C (Ideal.Quotient.mk n (θ i)))`. Introduce `n`.

Rewrite using `[← Polynomial.map_map, hQ, Polynomial.map_prod]`. Simplify using the standard rewrite rules. Establish `hcard : ∀ n : Ideal S, n.IsMaximal → (Finset.univ.filter (fun i => θ i ∈ n)).card = a`. Introduce `n hn`. Use `letI := Ideal.Quotient.field n`.

Use `data ((Ideal.Quotient.mk n).comp (algebraMap B S)) (by` as an intermediate fact. Introduce `b`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hkerI n hn b) Q (fun i => Ideal.Quotient.mk n (θ i)) (hmapn n)`. Simplify `this` using `[Ideal.Quotient.eq_zero_iff_mem]`.

Use `set r := Fintype.card σ - a with hr`. Establish `hcard' : ∀ n : Ideal S, n.IsMaximal → (Finset.univ.filter (fun i => θ i ∉ n)).card = r`. Introduce `n hn`. Establish `h1` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset σ)) (fun i => θ i ∈ n)`. Rewrite `h1` using `[hcard n hn, Finset.card_univ]`.

Use linear arithmetic over natural numbers and integers. Take `⟨F, hF⟩` from `exF σ Q r`. Establish `hFS` using `hF S (algebraMap B S) θ hQ`. Establish `hmonic : F.Monic`. Apply `Polynomial.monic_of_injective hinj` to reduce the goal to its premises.

Rewrite using `[hFS]`. Conclude with `Polynomial.monic_prod_of_monic _ _ (fun I _ => Polynomial.monic_X_sub_C _)`. Choose the witnesses or unpack the hypotheses as in `⟨τ, hτ0, hτm⟩ : ∃ τ : B, F.IsRoot τ ∧ τ ∉ IsLocalRing.maximalIdeal B := by`. Use `letI := Ideal.Quotient.field n2`. Set `ψ : B →+* S ⧸ n2` to `(Ideal.Quotient.mk n2).comp (algebraMap B S)`.

Set `θb : σ → S ⧸ n2` to `fun i => Ideal.Quotient.mk n2 (θ i)`. Establish `hzero : ∀ i, θb i = 0 ↔ θ i ∈ n2` using `fun i => Ideal.Quotient.eq_zero_iff_mem`. Establish `hψ : ∀ b, ψ b = 0 ↔ b ∈ IsLocalRing.maximalIdeal B`. Introduce `b`. Rewrite using `[RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hkerI n2 hn2 b`. Use `set I0 := Finset.univ.filter (fun i => θ i ∉ n2) with hI0`. Use `set c : S ⧸ n2 := ∏ i ∈ I0, θb i with hc`. Establish `hc0 : c ≠ 0`. Rewrite using `[hc, Finset.prod_ne_zero_iff]`.

Introduce `i hi`. Rewrite using `[Ne, hzero]`. Conclude with `(Finset.mem_filter.mp hi).2`. Use `set A : B := (-1) ^ r * Q.coeff a with hA`. Establish `hfil1 : Finset.univ.filter (fun i => θb i = 0) = Finset.univ.filter (fun i => θ i ∈ n2)`.

Use extensionality with `i`. Simplify using `[hzero]`. Establish `hfil2 : Finset.univ.filter (fun i => ¬ θb i = 0) = I0`. Use extensionality with `i`. Simplify using `[hzero, hI0]`.

Establish `hψA : ψ A = c`. Establish `h1` using `coeff_mid θb`. Rewrite `h1` using `[hfil1, hfil2, hcard n2 hn2, hcard' n2 hn2, ← hmapn n2, Polynomial.coeff_map]`. Establish `h3 : ψ (Q.coeff a) = (-1) ^ r * c` using `h1`. Rewrite using `[hA, map_mul, map_pow, map_neg, map_one, h3, ← mul_assoc, ← mul_pow]`.

Simplify using the standard rewrite rules. Establish `hFψ` using `hF (S ⧸ n2) ψ θb (hmapn n2)`. Establish `hI0mem : I0 ∈ Finset.powersetCard r (Finset.univ : Finset σ)` using `Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard' n2 hn2⟩`. Rewrite `hFψ` using `[← Finset.mul_prod_erase _ _ hI0mem]`. Use `set G : Polynomial (S ⧸ n2) := ∏ I ∈ (Finset.powersetCard r (Finset.univ : Finset σ)).erase I0, (Polynomial.X - Polynomial.C (∏ i ∈ I, θb i)) with hG`.

Establish `hGc : G.eval c ≠ 0`. Rewrite using `[hG, Polynomial.eval_prod, Finset.prod_ne_zero_iff]`. Introduce `I hI`. Take `⟨hne, hIm⟩` from `Finset.mem_erase.mp hI`. Take `⟨-, hIc⟩` from `Finset.mem_powersetCard.mp hIm`.

Establish `hnot : ¬ I ⊆ I0` using `fun hs => hne (Finset.eq_of_subset_of_card_le hs (by rw [hIc, hcard' n2 hn2]))`. Take `⟨i, hiI, hiI0⟩` from `Finset.not_subset.mp hnot`. Establish `hz : θb i = 0`. Rewrite using `[hzero]`. Assume the negation of the conclusion as `hcon`.

Conclude with `hiI0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)`. Rewrite using `[Finset.prod_eq_zero hiI hz]`. Simplify using `using hc0`. Establish `hev : (F.map ψ).eval c = 0`. Rewrite using `[hFψ, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]`.

Establish `hder : (Polynomial.derivative (F.map ψ)).eval c ≠ 0`. Rewrite using `[hFψ, Polynomial.derivative_mul]`. Simplify using `only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]`. Rewrite using `[show c - ∏ i ∈ I0, θb i = 0 from sub_self _, zero_mul, add_zero]`. Conclude with `hGc`.

Establish `h1 : F.eval A ∈ IsLocalRing.maximalIdeal B`. Rewrite using `[← hψ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hψA]`. Conclude with `hev`. Establish `h2' : IsUnit ((Polynomial.derivative F).eval A)`. Assume the negation of the conclusion as `hcon`.

Establish `hm : (Polynomial.derivative F).eval A ∈ IsLocalRing.maximalIdeal B` using `(IsLocalRing.mem_maximalIdeal _).mpr hcon`. Rewrite `hm` using `[← hψ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hψA, ← Polynomial.derivative_map]`. Conclude with `hder hm`. Take `⟨τ, hτ, hτA⟩` from `HenselianLocalRing.is_henselian F hmonic A h1 h2'`. Use `⟨τ, hτ, fun hm => ?_⟩` and prove the remaining obligations.

Establish `: A ∈ IsLocalRing.maximalIdeal B`. Use `Ideal.sub_mem _ hm hτA` as an intermediate fact. Simplify using `using this`. Rewrite `this` using `[← hψ, hψA]`. Conclude with `hc0 this`.

Establish `hev : (F.map (algebraMap B S)).eval (algebraMap B S τ) = 0`. Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply, hτ0.eq_zero, map_zero]`. Rewrite `hev` using `[hFS, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨I, hI, hIτ⟩` from `hev`. Establish `hτI : algebraMap B S τ = ∏ i ∈ I, θ i`.

Rewrite `hIτ` using `[Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero]`. Then use the resulting hypothesis. Take `⟨-, hIc⟩` from `Finset.mem_powersetCard.mp hI`. Establish `hIeq : ∀ n : Ideal S, n.IsMaximal → I = Finset.univ.filter (fun i => θ i ∉ n)`. Introduce `n hn`. Use `Finset.eq_of_subset_of_card_le ?_ (by rw [hIc, hcard' n hn])` and prove the remaining obligations.

Introduce `i hi`. Use `Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hin => hτm ?_⟩` and prove the remaining obligations. Rewrite using `[← hkerI n hn, hτI]`. Conclude with `Ideal.mem_of_dvd n (Finset.dvd_prod_of_mem θ hi) hin`. Establish `hi0 : i0 ∈ I`.

Rewrite using `[hIeq n2 hn2]`. Conclude with `Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩`. Rewrite `hi0` using `[hIeq n1 hn1]`. Conclude with `(Finset.mem_filter.mp hi0).2`.
-/
private theorem key {B S : Type} [CommRing B] [HenselianLocalRing B] [CommRing S] [IsDomain S]
    [Algebra B S] [Algebra.IsIntegral B S] (hinj : Function.Injective (algebraMap B S))
    {σ : Type} [Fintype σ] (Q : Polynomial B) (θ : σ → S)
    (hQ : Q.map (algebraMap B S) = ∏ i, (Polynomial.X - Polynomial.C (θ i)))
    (n1 n2 : Ideal S) (hn1 : n1.IsMaximal) (hn2 : n2.IsMaximal) (i0 : σ) (h2 : θ i0 ∉ n2) :
    θ i0 ∉ n1 := by
  classical
  have hcomap : ∀ n : Ideal S, n.IsMaximal →
      n.comap (algebraMap B S) = IsLocalRing.maximalIdeal B := by
    intro n hn
    have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := B) n
    exact IsLocalRing.eq_maximalIdeal this
  have hkerI : ∀ n : Ideal S, n.IsMaximal → ∀ b, algebraMap B S b ∈ n ↔ b ∈ IsLocalRing.maximalIdeal B := by
    intro n hn b
    rw [← hcomap n hn, Ideal.mem_comap]
  set a := (Q.map (IsLocalRing.residue B)).rootMultiplicity 0 with ha
  have hmapn : ∀ n : Ideal S, Q.map ((Ideal.Quotient.mk n).comp (algebraMap B S)) =
      ∏ i, (Polynomial.X - Polynomial.C (Ideal.Quotient.mk n (θ i))) := by
    intro n
    rw [← Polynomial.map_map, hQ, Polynomial.map_prod]
    simp
  have hcard : ∀ n : Ideal S, n.IsMaximal → (Finset.univ.filter (fun i => θ i ∈ n)).card = a := by
    intro n hn
    letI := Ideal.Quotient.field n
    have := data ((Ideal.Quotient.mk n).comp (algebraMap B S)) (by
      intro b
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hkerI n hn b) Q (fun i => Ideal.Quotient.mk n (θ i)) (hmapn n)
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this
  set r := Fintype.card σ - a with hr
  have hcard' : ∀ n : Ideal S, n.IsMaximal → (Finset.univ.filter (fun i => θ i ∉ n)).card = r := by
    intro n hn
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset σ)) (fun i => θ i ∈ n)
    rw [hcard n hn, Finset.card_univ] at h1
    omega
  obtain ⟨F, hF⟩ := exF σ Q r
  have hFS := hF S (algebraMap B S) θ hQ
  have hmonic : F.Monic := by
    apply Polynomial.monic_of_injective hinj
    rw [hFS]
    exact Polynomial.monic_prod_of_monic _ _ (fun I _ => Polynomial.monic_X_sub_C _)
  obtain ⟨τ, hτ0, hτm⟩ : ∃ τ : B, F.IsRoot τ ∧ τ ∉ IsLocalRing.maximalIdeal B := by
    letI := Ideal.Quotient.field n2
    let ψ : B →+* S ⧸ n2 := (Ideal.Quotient.mk n2).comp (algebraMap B S)
    let θb : σ → S ⧸ n2 := fun i => Ideal.Quotient.mk n2 (θ i)
    have hzero : ∀ i, θb i = 0 ↔ θ i ∈ n2 := fun i => Ideal.Quotient.eq_zero_iff_mem
    have hψ : ∀ b, ψ b = 0 ↔ b ∈ IsLocalRing.maximalIdeal B := by
      intro b
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hkerI n2 hn2 b
    set I0 := Finset.univ.filter (fun i => θ i ∉ n2) with hI0
    set c : S ⧸ n2 := ∏ i ∈ I0, θb i with hc
    have hc0 : c ≠ 0 := by
      rw [hc, Finset.prod_ne_zero_iff]
      intro i hi
      rw [Ne, hzero]
      exact (Finset.mem_filter.mp hi).2
    set A : B := (-1) ^ r * Q.coeff a with hA
    have hfil1 : Finset.univ.filter (fun i => θb i = 0) = Finset.univ.filter (fun i => θ i ∈ n2) := by
      ext i; simp [hzero]
    have hfil2 : Finset.univ.filter (fun i => ¬ θb i = 0) = I0 := by
      ext i; simp [hzero, hI0]
    have hψA : ψ A = c := by
      have h1 := coeff_mid θb
      rw [hfil1, hfil2, hcard n2 hn2, hcard' n2 hn2, ← hmapn n2, Polynomial.coeff_map] at h1
      have h3 : ψ (Q.coeff a) = (-1) ^ r * c := h1
      rw [hA, map_mul, map_pow, map_neg, map_one, h3, ← mul_assoc, ← mul_pow]
      simp
    have hFψ := hF (S ⧸ n2) ψ θb (hmapn n2)
    have hI0mem : I0 ∈ Finset.powersetCard r (Finset.univ : Finset σ) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard' n2 hn2⟩
    rw [← Finset.mul_prod_erase _ _ hI0mem] at hFψ
    set G : Polynomial (S ⧸ n2) := ∏ I ∈ (Finset.powersetCard r (Finset.univ : Finset σ)).erase I0,
      (Polynomial.X - Polynomial.C (∏ i ∈ I, θb i)) with hG
    have hGc : G.eval c ≠ 0 := by
      rw [hG, Polynomial.eval_prod, Finset.prod_ne_zero_iff]
      intro I hI
      obtain ⟨hne, hIm⟩ := Finset.mem_erase.mp hI
      obtain ⟨-, hIc⟩ := Finset.mem_powersetCard.mp hIm
      have hnot : ¬ I ⊆ I0 := fun hs =>
        hne (Finset.eq_of_subset_of_card_le hs (by rw [hIc, hcard' n2 hn2]))
      obtain ⟨i, hiI, hiI0⟩ := Finset.not_subset.mp hnot
      have hz : θb i = 0 := by
        rw [hzero]
        by_contra hcon
        exact hiI0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩)
      rw [Finset.prod_eq_zero hiI hz]
      simpa using hc0
    have hev : (F.map ψ).eval c = 0 := by
      rw [hFψ, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul]
    have hder : (Polynomial.derivative (F.map ψ)).eval c ≠ 0 := by
      rw [hFψ, Polynomial.derivative_mul]
      simp only [Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero, one_mul, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, add_zero]
      rw [show c - ∏ i ∈ I0, θb i = 0 from sub_self _, zero_mul, add_zero]
      exact hGc
    have h1 : F.eval A ∈ IsLocalRing.maximalIdeal B := by
      rw [← hψ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hψA]
      exact hev
    have h2' : IsUnit ((Polynomial.derivative F).eval A) := by
      by_contra hcon
      have hm : (Polynomial.derivative F).eval A ∈ IsLocalRing.maximalIdeal B :=
        (IsLocalRing.mem_maximalIdeal _).mpr hcon
      rw [← hψ, ← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hψA, ← Polynomial.derivative_map] at hm
      exact hder hm
    obtain ⟨τ, hτ, hτA⟩ := HenselianLocalRing.is_henselian F hmonic A h1 h2'
    refine ⟨τ, hτ, fun hm => ?_⟩
    have : A ∈ IsLocalRing.maximalIdeal B := by
      have := Ideal.sub_mem _ hm hτA
      simpa using this
    rw [← hψ, hψA] at this
    exact hc0 this
  have hev : (F.map (algebraMap B S)).eval (algebraMap B S τ) = 0 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hτ0.eq_zero, map_zero]
  rw [hFS, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at hev
  obtain ⟨I, hI, hIτ⟩ := hev
  have hτI : algebraMap B S τ = ∏ i ∈ I, θ i := by
    rwa [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hIτ
  obtain ⟨-, hIc⟩ := Finset.mem_powersetCard.mp hI
  have hIeq : ∀ n : Ideal S, n.IsMaximal → I = Finset.univ.filter (fun i => θ i ∉ n) := by
    intro n hn
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hIc, hcard' n hn])
    intro i hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hin => hτm ?_⟩
    rw [← hkerI n hn, hτI]
    exact Ideal.mem_of_dvd n (Finset.dvd_prod_of_mem θ hi) hin
  have hi0 : i0 ∈ I := by
    rw [hIeq n2 hn2]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2⟩
  rw [hIeq n1 hn1] at hi0
  exact (Finset.mem_filter.mp hi0).2

/- English proof (translation)
Establish `hp : (RingHom.ker f).IsPrime` using `RingHom.ker_isPrime f`. Take `⟨P, -, hP, hc⟩` from `Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f) (⊥ : Ideal S) (by`. Introduce `b hb`. Establish `: algebraMap B S b = 0` using `hb`. Establish `hb0 : b = 0` using `hinj (by rw [this, map_zero])`.

Rewrite using `[hb0]`. Conclude with `Ideal.zero_mem _)`. Use `set q := P.comap (algebraMap B S) with hq`. Establish `hqk : ∀ b ∈ q, f b = 0`. Introduce `b hb`.

Rewrite `hb` using `[hc]`. Conclude with `hb`. Set `f1 : B ⧸ q →+* C` to `Ideal.Quotient.lift q f hqk`. Establish `hf1 : Function.Injective f1`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `a ha`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Establish `: b ∈ q` using `by rw [hc]; exact ha`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr this`. Use `letI : Algebra (B ⧸ q) C := f1.toAlgebra`.

Establish `hi : Function.Injective (algebraMap (B ⧸ q) (S ⧸ P))`. Conclude with `Ideal.algebraMap_quotient_injective`. Use `haveI : Algebra.IsIntegral (B ⧸ q) (S ⧸ P) := .tower_top B`. Use `haveI : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q`. Use `haveI : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P`.

Use `haveI : Module.IsTorsionFree (B ⧸ q) (S ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.mpr hi`. Use `haveI : Module.IsTorsionFree (B ⧸ q) C := Module.isTorsionFree_iff_algebraMap_injective.mpr hf1`. Use `haveI : Algebra.IsAlgebraic (B ⧸ q) (S ⧸ P) := Algebra.IsIntegral.isAlgebraic`. Set `L : (S ⧸ P) →ₐ[B ⧸ q] C` to `IsAlgClosed.lift`. Use `⟨(L : (S ⧸ P) →+* C).comp (Ideal.Quotient.mk P), ?_⟩` and prove the remaining obligations.

Use extensionality with `b`. Establish `h1 : Ideal.Quotient.mk P (algebraMap B S b) = algebraMap (B ⧸ q) (S ⧸ P) (Ideal.Quotient.mk q b)` using `rfl`. Simplify using `only [RingHom.comp_apply, RingHom.coe_coe]`. Rewrite using `[h1, L.commutes]`. Both sides reduce to the same expression.
-/
private theorem ext_hom {B S C : Type} [CommRing B] [CommRing S] [Algebra B S] [Algebra.IsIntegral B S]
    (hinj : Function.Injective (algebraMap B S)) [Field C] [IsAlgClosed C] (f : B →+* C) :
    ∃ g : S →+* C, g.comp (algebraMap B S) = f := by
  have hp : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨P, -, hP, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f) (⊥ : Ideal S)
    (by
      intro b hb
      have : algebraMap B S b = 0 := hb
      have hb0 : b = 0 := hinj (by rw [this, map_zero])
      rw [hb0]; exact Ideal.zero_mem _)
  set q := P.comap (algebraMap B S) with hq
  have hqk : ∀ b ∈ q, f b = 0 := by
    intro b hb
    rw [hc] at hb
    exact hb
  let f1 : B ⧸ q →+* C := Ideal.Quotient.lift q f hqk
  have hf1 : Function.Injective f1 := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    have : b ∈ q := by rw [hc]; exact ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  letI : Algebra (B ⧸ q) C := f1.toAlgebra
  have hi : Function.Injective (algebraMap (B ⧸ q) (S ⧸ P)) := by
    exact Ideal.algebraMap_quotient_injective
  haveI : Algebra.IsIntegral (B ⧸ q) (S ⧸ P) := .tower_top B
  haveI : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q
  haveI : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Module.IsTorsionFree (B ⧸ q) (S ⧸ P) := Module.isTorsionFree_iff_algebraMap_injective.mpr hi
  haveI : Module.IsTorsionFree (B ⧸ q) C := Module.isTorsionFree_iff_algebraMap_injective.mpr hf1
  haveI : Algebra.IsAlgebraic (B ⧸ q) (S ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let L : (S ⧸ P) →ₐ[B ⧸ q] C := IsAlgClosed.lift
  refine ⟨(L : (S ⧸ P) →+* C).comp (Ideal.Quotient.mk P), ?_⟩
  ext b
  have h1 : Ideal.Quotient.mk P (algebraMap B S b) = algebraMap (B ⧸ q) (S ⧸ P) (Ideal.Quotient.mk q b) := rfl
  simp only [RingHom.comp_apply, RingHom.coe_coe]
  rw [h1, L.commutes]
  rfl

/- English proof (translation)
Establish `hκ0 : κ ≠ 0`. Introduce `h`. Rewrite `hκ` using `[h, norm_zero]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set w := κ⁻¹ with hw`.

Establish `hwn : ‖w‖ ≤ 1`. Rewrite using `[hw, norm_inv]`. Conclude with `inv_le_one_of_one_le₀ hκ`. Establish `hint : IsIntegral ℚ_[l] w` using `Algebra.IsIntegral.isIntegral w`. Establish `hm : (minpoly ℚ_[l] w).Monic` using `minpoly.monic hint`.

Establish `hs : spectralValue (minpoly ℚ_[l] w) ≤ 1` using `hwn`. Establish `hc` using `(spectralValue_le_one_iff hm).mp hs`. Establish `hl : minpoly ℚ_[l] w ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hl hm`. Use `⟨q.reverse, ?_, ?_⟩` and prove the remaining obligations. Use `letI : Invertible w := invertibleOfNonzero (inv_ne_zero hκ0)`. Establish `h1` using `Polynomial.eval₂_reverse_mul_pow ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) w q`.

Establish `h2 : Polynomial.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) w q = 0`. Rewrite using `[← Polynomial.eval₂_map, hq]`. Conclude with `minpoly.aeval ℚ_[l] w`. Establish `h3 : ⅟w = κ`. Rewrite using `[invOf_eq_inv, hw, inv_inv]`.

Rewrite `h1` using `[h2, h3]`. Break down `mul_eq_zero.mp h1 with h4 | h4` into its components or cases. Conclude with `h4`. Conclude with `absurd h4 (pow_ne_zero _ (inv_ne_zero hκ0))`. Rewrite using `[Polynomial.coeff_zero_reverse]`.

Conclude with `hqm`.
-/
private theorem loc_hom {l : ℕ} [Fact (Nat.Prime l)] (κ : PadicAlgCl l) (hκ : 1 ≤ ‖κ‖) :
    ∃ h : Polynomial ℤ_[l], h.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) κ = 0 ∧
      h.coeff 0 = 1 := by
  have hκ0 : κ ≠ 0 := by
    intro h; rw [h, norm_zero] at hκ; linarith
  set w := κ⁻¹ with hw
  have hwn : ‖w‖ ≤ 1 := by
    rw [hw, norm_inv]
    exact inv_le_one_of_one_le₀ hκ
  have hint : IsIntegral ℚ_[l] w := Algebra.IsIntegral.isIntegral w
  have hm : (minpoly ℚ_[l] w).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] w) ≤ 1 := hwn
  have hc := (spectralValue_le_one_iff hm).mp hs
  have hl : minpoly ℚ_[l] w ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q.reverse, ?_, ?_⟩
  · letI : Invertible w := invertibleOfNonzero (inv_ne_zero hκ0)
    have h1 := Polynomial.eval₂_reverse_mul_pow ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) w q
    have h2 : Polynomial.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) w q = 0 := by
      rw [← Polynomial.eval₂_map, hq]
      exact minpoly.aeval ℚ_[l] w
    have h3 : ⅟w = κ := by
      rw [invOf_eq_inv, hw, inv_inv]
    rw [h2, h3] at h1
    rcases mul_eq_zero.mp h1 with h4 | h4
    · exact h4
    · exact absurd h4 (pow_ne_zero _ (inv_ne_zero hκ0))
  · rw [Polynomial.coeff_zero_reverse]
    exact hqm

/- English proof (translation)
Set `K` to `FractionRing B`. Set `Ω` to `AlgebraicClosure K`. Set `S` to `integralClosure B Ω`. Establish `hinjΩ : Function.Injective (algebraMap B Ω)`. Rewrite using `[IsScalarTower.algebraMap_eq B K Ω]`.

Conclude with `(algebraMap K Ω).injective.comp (IsFractionRing.injective B K)`. Establish `hinj : Function.Injective (algebraMap B S)`. Introduce `a b hab`. Conclude with `hinjΩ (congrArg Subtype.val hab)`. Use `haveI hI : Algebra.IsIntegral B S := inferInstance`.

Establish `hkey : ∀ (θ0 : S) (n n' : Ideal S), n.IsMaximal → n'.IsMaximal → θ0 ∉ n → θ0 ∉ n'`. Introduce `θ0 n n' hn hn' h0`. Take `⟨Q, hQm, hQ0⟩` from `Algebra.IsIntegral.isIntegral (R := B) θ0`. Use `set s := (Q.map (algebraMap B Ω)).roots with hs`. Establish `hsp : Q.map (algebraMap B Ω) = (s.map (fun a => Polynomial.X - Polynomial.C a)).prod` using `(IsAlgClosed.splits _).eq_prod_roots_of_monic (hQm.map _)`.

Establish `hint : ∀ z ∈ s, z ∈ S`. Introduce `z hz`. Establish `hz'` using `(Polynomial.mem_roots'.mp hz).2`. Use `⟨Q, hQm, ?_⟩` and prove the remaining obligations. Rewrite `hz'` using `[Polynomial.IsRoot.def, Polynomial.eval_map]`.

Conclude with `hz'`. Set `s' : Multiset S` to `s.attach.map (fun z => ⟨z.1, hint z.1 z.2⟩)`. Establish `hs' : s'.map (algebraMap S Ω) = s`. Simplify using `only [s', Multiset.map_map]`. Conclude with `Multiset.attach_map_val s`.

Establish `hQS : Q.map (algebraMap B S) = (s'.map (fun a => Polynomial.X - Polynomial.C a)).prod`. Apply `Polynomial.map_injective (algebraMap S Ω) Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hsp, Polynomial.map_multiset_prod, Multiset.map_map]`. Use `conv_lhs => rw [← hs']`. Rewrite using `[Multiset.map_map]`.

Simplify using the standard rewrite rules. Both sides reduce to the same expression. Set `θ : s' → S` to `fun i => (i : S)`. Establish `hprod : Q.map (algebraMap B S) = ∏ i, (Polynomial.X - Polynomial.C (θ i))`. Rewrite using `[hQS, Finset.prod_eq_multiset_prod]`.

Use `conv_lhs => rw [← Multiset.map_univ_coe s']`. Rewrite using `[Multiset.map_map]`. Both sides reduce to the same expression. Establish `hroot : ∃ i, θ0 = θ i`. Establish `h1 : (Q.map (algebraMap B S)).eval θ0 = 0`.

Rewrite using `[Polynomial.eval_map]`. Conclude with `hQ0`. Rewrite `h1` using `[hprod, Polynomial.eval_prod, Finset.prod_eq_zero_iff]`. Take `⟨i, -, hi⟩` from `h1`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Simplify `hi` using `[sub_eq_zero]`. Take `⟨i, rfl⟩` from `hroot`. Conclude with `key hinj Q θ hprod n' n hn' hn i h0`. Establish `hloc : IsLocalRing S`. Take `⟨n, hn⟩` from `Ideal.exists_maximal S`.

Use `IsLocalRing.of_unique_max_ideal ⟨n, hn, fun n' hn' => ?_⟩` and prove the remaining obligations. Use `hn'.eq_of_le hn.ne_top ?_` and prove the remaining obligations. Introduce `z hz`. Assume the negation of the conclusion as `hcon`. Conclude with `hkey z n n' hn hn' hcon hz`.

Use `⟨S, inferInstance, inferInstance, inferInstance, hI, hloc, hinj, ⟨algebraMap K Ω v, hv.algebraMap⟩, ?_⟩` and prove the remaining obligations. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (algebraMap K Ω) hab` as an intermediate fact. Rewrite `this` using `[map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.

Conclude with `this`.
-/
private theorem cl_exists {B : Type} [CommRing B] [IsDomain B] [HenselianLocalRing B] (v : FractionRing B)
    (hv : IsIntegral B v) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra B S), IsDomain S ∧ Algebra.IsIntegral B S ∧
      IsLocalRing S ∧ Function.Injective (algebraMap B S) ∧
      ∃ vS : S, ∀ a b : B, algebraMap B (FractionRing B) a * v = algebraMap B (FractionRing B) b →
        algebraMap B S a * vS = algebraMap B S b := by
  classical
  let K := FractionRing B
  let Ω := AlgebraicClosure K
  let S := integralClosure B Ω
  have hinjΩ : Function.Injective (algebraMap B Ω) := by
    rw [IsScalarTower.algebraMap_eq B K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective B K)
  have hinj : Function.Injective (algebraMap B S) := by
    intro a b hab
    exact hinjΩ (congrArg Subtype.val hab)
  haveI hI : Algebra.IsIntegral B S := inferInstance
  have hkey : ∀ (θ0 : S) (n n' : Ideal S), n.IsMaximal → n'.IsMaximal → θ0 ∉ n → θ0 ∉ n' := by
    intro θ0 n n' hn hn' h0
    obtain ⟨Q, hQm, hQ0⟩ := Algebra.IsIntegral.isIntegral (R := B) θ0
    set s := (Q.map (algebraMap B Ω)).roots with hs
    have hsp : Q.map (algebraMap B Ω) = (s.map (fun a => Polynomial.X - Polynomial.C a)).prod :=
      (IsAlgClosed.splits _).eq_prod_roots_of_monic (hQm.map _)
    have hint : ∀ z ∈ s, z ∈ S := by
      intro z hz
      have hz' := (Polynomial.mem_roots'.mp hz).2
      refine ⟨Q, hQm, ?_⟩
      rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hz'
      exact hz'
    let s' : Multiset S := s.attach.map (fun z => ⟨z.1, hint z.1 z.2⟩)
    have hs' : s'.map (algebraMap S Ω) = s := by
      simp only [s', Multiset.map_map]
      exact Multiset.attach_map_val s
    have hQS : Q.map (algebraMap B S) = (s'.map (fun a => Polynomial.X - Polynomial.C a)).prod := by
      apply Polynomial.map_injective (algebraMap S Ω) Subtype.val_injective
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, hsp, Polynomial.map_multiset_prod, Multiset.map_map]
      conv_lhs => rw [← hs']
      rw [Multiset.map_map]
      simp
      rfl
    let θ : s' → S := fun i => (i : S)
    have hprod : Q.map (algebraMap B S) = ∏ i, (Polynomial.X - Polynomial.C (θ i)) := by
      rw [hQS, Finset.prod_eq_multiset_prod]
      conv_lhs => rw [← Multiset.map_univ_coe s']
      rw [Multiset.map_map]
      rfl
    have hroot : ∃ i, θ0 = θ i := by
      have h1 : (Q.map (algebraMap B S)).eval θ0 = 0 := by
        rw [Polynomial.eval_map]; exact hQ0
      rw [hprod, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h1
      obtain ⟨i, -, hi⟩ := h1
      refine ⟨i, ?_⟩
      simpa [sub_eq_zero] using hi
    obtain ⟨i, rfl⟩ := hroot
    exact key hinj Q θ hprod n' n hn' hn i h0
  have hloc : IsLocalRing S := by
    obtain ⟨n, hn⟩ := Ideal.exists_maximal S
    refine IsLocalRing.of_unique_max_ideal ⟨n, hn, fun n' hn' => ?_⟩
    refine hn'.eq_of_le hn.ne_top ?_
    intro z hz
    by_contra hcon
    exact hkey z n n' hn hn' hcon hz
  refine ⟨S, inferInstance, inferInstance, inferInstance, hI, hloc, hinj,
    ⟨algebraMap K Ω v, hv.algebraMap⟩, ?_⟩
  intro a b hab
  apply Subtype.ext
  have := congrArg (algebraMap K Ω) hab
  rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
  exact this

/- English proof (translation)
Introduce `l _ O B _ _ _ _ _ _ _ _ x y d hd t hxt v hv hdv κ hκ`. Assume the negation of the conclusion as `hlt`. Establish `hκ1 : 1 ≤ ‖κ‖` using `not_lt.mp hlt`. Take `⟨S, _, _, hdom, hintg, hloc, hinj, vS, hrel⟩` from `cl_exists (B := B) v hv`. Take `⟨gx, hgx⟩` from `ext_hom hinj (x : B →+* PadicAlgCl l)`.

Take `⟨gy, hgy⟩` from `ext_hom hinj (y : B →+* PadicAlgCl l)`. Establish `ex : ∀ b, gx (algebraMap B S b) = x b` using `fun b => by`. Rewrite using `[← RingHom.comp_apply, hgx]`. Both sides reduce to the same expression. Establish `ey : ∀ b, gy (algebraMap B S b) = y b` using `fun b => by`.

Rewrite using `[← RingHom.comp_apply, hgy]`. Both sides reduce to the same expression. Establish `hd' : algebraMap O (PadicAlgCl l) d ≠ 0` using `hd`. Establish `hκ' : algebraMap O (PadicAlgCl l) d * κ = y t` using `hκ`. Establish `hS : algebraMap B S (algebraMap O B d) * vS = algebraMap B S t` using `hrel _ _ hdv`.

Establish `h1 : gx vS = 0`. Use `congrArg gx hS` as an intermediate fact. Rewrite `this` using `[map_mul, ex, ex, x.commutes, hxt]`. Conclude with `(mul_eq_zero.mp this).resolve_left hd'`. Establish `h2 : gy vS = κ`.

Use `congrArg gy hS` as an intermediate fact. Rewrite `this` using `[map_mul, ey, ey, y.commutes, ← hκ']`. Conclude with `mul_left_cancel₀ hd' this`. Establish `hvS : vS ∈ IsLocalRing.maximalIdeal S`. Rewrite using `[IsLocalRing.mem_maximalIdeal]`.

Introduce `hu`. Use `hu.map gx` as an intermediate fact. Rewrite `this` using `[h1]`. Conclude with `not_isUnit_zero this`. Take `⟨h, hh0, hh1⟩` from `loc_hom κ hκ1`.

Set `φ : ℤ_[l] →+* S` to `(algebraMap B S).comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))`. Establish `hφ : gy.comp φ = (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])`. Use extensionality with `a`. Simplify using `only [φ, RingHom.comp_apply]`. Rewrite using `[ey, y.commutes, ← IsScalarTower.algebraMap_apply]`.

Both sides reduce to the same expression. Use `set w := Polynomial.eval₂ φ vS h with hw`. Establish `hyw : gy w = 0`. Rewrite using `[hw, Polynomial.hom_eval₂, hφ, h2]`. Conclude with `hh0`.

Establish `hwm : w ∈ IsLocalRing.maximalIdeal S`. Rewrite using `[IsLocalRing.mem_maximalIdeal]`. Introduce `hu`. Use `hu.map gy` as an intermediate fact. Rewrite `this` using `[hyw]`.

Conclude with `not_isUnit_zero this`. Establish `hw1 : w = Polynomial.eval₂ φ vS h.divX * vS + 1` using `by conv_lhs => rw [hw, ← Polynomial.divX_mul_X_add h, hh1]`. Simplify using `[Polynomial.eval₂_add, Polynomial.eval₂_mul]`. Establish `hone : (1 : S) ∈ IsLocalRing.maximalIdeal S`. Establish `h3` using `Ideal.sub_mem _ hwm (Ideal.mul_mem_left _ (Polynomial.eval₂ φ vS h.divX) hvS)`.

Rewrite `h3` using `[hw1]`. Simplify using `using h3`. Conclude with `(Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal S).ne_top hone`.
-/
theorem UpperTheory.Reformulated.B.MajorantSquareBound.spl_near :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O B : Type}
    [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] [inst_3 : Algebra O (PadicAlgCl l)]
    [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [inst_5 : CommRing B] [IsDomain B] [HenselianLocalRing B]
    [inst_8 : Algebra O B] (x y : B →ₐ[O] PadicAlgCl l) (d : O),
    (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d ≠ (0 : PadicAlgCl l) →
      ∀ (t : B),
        (x : B → PadicAlgCl l) t = (0 : PadicAlgCl l) →
          ∀ (v : FractionRing B),
            IsIntegral B v →
              (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) ((Algebra.algebraMap O B : O → B) d) * v =
                  (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) t →
                ∀ (κ : PadicAlgCl l),
                  (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d * κ = (y : B → PadicAlgCl l) t →
                    ‖κ‖ < (1 : ℝ) := by
  intro l _ O B _ _ _ _ _ _ _ _ x y d hd t hxt v hv hdv κ hκ
  by_contra hlt
  have hκ1 : 1 ≤ ‖κ‖ := not_lt.mp hlt
  obtain ⟨S, _, _, hdom, hintg, hloc, hinj, vS, hrel⟩ := cl_exists (B := B) v hv
  obtain ⟨gx, hgx⟩ := ext_hom hinj (x : B →+* PadicAlgCl l)
  obtain ⟨gy, hgy⟩ := ext_hom hinj (y : B →+* PadicAlgCl l)
  have ex : ∀ b, gx (algebraMap B S b) = x b := fun b => by
    rw [← RingHom.comp_apply, hgx]; rfl
  have ey : ∀ b, gy (algebraMap B S b) = y b := fun b => by
    rw [← RingHom.comp_apply, hgy]; rfl
  have hd' : algebraMap O (PadicAlgCl l) d ≠ 0 := hd
  have hκ' : algebraMap O (PadicAlgCl l) d * κ = y t := hκ
  have hS : algebraMap B S (algebraMap O B d) * vS = algebraMap B S t := hrel _ _ hdv
  have h1 : gx vS = 0 := by
    have := congrArg gx hS
    rw [map_mul, ex, ex, x.commutes, hxt] at this
    exact (mul_eq_zero.mp this).resolve_left hd'
  have h2 : gy vS = κ := by
    have := congrArg gy hS
    rw [map_mul, ey, ey, y.commutes, ← hκ'] at this
    exact mul_left_cancel₀ hd' this
  have hvS : vS ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have := hu.map gx
    rw [h1] at this
    exact not_isUnit_zero this
  obtain ⟨h, hh0, hh1⟩ := loc_hom κ hκ1
  let φ : ℤ_[l] →+* S := (algebraMap B S).comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))
  have hφ : gy.comp φ = (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l]) := by
    ext a
    simp only [φ, RingHom.comp_apply]
    rw [ey, y.commutes, ← IsScalarTower.algebraMap_apply]
    rfl
  set w := Polynomial.eval₂ φ vS h with hw
  have hyw : gy w = 0 := by
    rw [hw, Polynomial.hom_eval₂, hφ, h2]
    exact hh0
  have hwm : w ∈ IsLocalRing.maximalIdeal S := by
    rw [IsLocalRing.mem_maximalIdeal]
    intro hu
    have := hu.map gy
    rw [hyw] at this
    exact not_isUnit_zero this
  have hw1 : w = Polynomial.eval₂ φ vS h.divX * vS + 1 := by
    conv_lhs => rw [hw, ← Polynomial.divX_mul_X_add h, hh1]
    simp [Polynomial.eval₂_add, Polynomial.eval₂_mul]
  have hone : (1 : S) ∈ IsLocalRing.maximalIdeal S := by
    have h3 := Ideal.sub_mem _ hwm (Ideal.mul_mem_left _ (Polynomial.eval₂ φ vS h.divX) hvS)
    rw [hw1] at h3
    simpa using h3
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal S).ne_top hone
