import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn

noncomputable section

open Finset Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.OmegaPQAux

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

section gen

variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]

/- English proof (translation)
Establish `e1` using `measurePreserving_prodAssoc μa μb (μc.prod μd)`. Establish `e2` using `(MeasurePreserving.id μa).prod (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd))`. Establish `e3` using `(MeasurePreserving.id μa).prod ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))`. Establish `e4` using `(MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)`. Establish `e5` using `MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μa μc (μb.prod μd))`.

Conclude with `e5.comp (e4.comp (e3.comp (e2.comp e1)))`.
-/
theorem mp_ppc (μa : Measure α) (μb : Measure β) (μc : Measure γ) (μd : Measure δ)
    [SigmaFinite μa] [SigmaFinite μb] [SigmaFinite μc] [SigmaFinite μd] :
    MeasurePreserving (fun x : (α × β) × (γ × δ) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      ((μa.prod μb).prod (μc.prod μd)) ((μa.prod μc).prod (μb.prod μd)) := by
  have e1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have e2 := (MeasurePreserving.id μa).prod
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μb μc μd))
  have e3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have e4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have e5 := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μa μc (μb.prod μd))
  exact e5.comp (e4.comp (e3.comp (e2.comp e1)))

end gen

variable {n : ℕ}

abbrev Qp (ε : Fin n → Bool) : Type := KPair ε ⊕ PCoord ε

def idxFun (ε : Fin n → Bool) : Fin n ⊕ (Qp ε ⊕ Qp ε) → Fin n × Fin n
  | Sum.inl a => (a, a)
  | Sum.inr (Sum.inl (Sum.inl k)) => k.1
  | Sum.inr (Sum.inl (Sum.inr p)) => p.1
  | Sum.inr (Sum.inr (Sum.inl k)) => k.1.swap
  | Sum.inr (Sum.inr (Sum.inr p)) => p.1.swap

/- English proof (translation)
Rewrite using `[Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]`. Simplify using `only [ne_eq]`. Rewrite using `[← Finset.filter_filter, ← Finset.filter_filter]`. Establish `key : ∀ x : Fin n × Fin n, ((if ε x.1 = ε x.2 then 1 else 0) + (if ¬ε x.1 = ε x.2 then 1 else 0) : ℕ) = 1`. Introduce `x`.

Apply the tactic sequence `split_ifs <;> simp_all`. Simplify using `only [Finset.card_filter (fun x : Fin n × Fin n => ε x.1 = ε x.2), Finset.card_filter (fun x : Fin n × Fin n => ¬ε x.1 = ε x.2), ← Finset.sum_add_distrib, key, Finset.sum_const, smul_eq_mul, mul_one]`. Rewrite using `[Finset.card_filter, Fintype.sum_prod_type]`. Establish `h1 : ∀ a : Fin n, (∑ b : Fin n, if b < a then 1 else 0) = (a : ℕ)`. Introduce `a`.

Rewrite using `[← Finset.card_filter]`. Establish `: (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a`. Use extensionality with `b`. Simplify using the standard rewrite rules. Rewrite using `[this, Fin.card_Iio]`.

Simplify using `only [h1]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]`.
-/
private theorem card_qp_eq_mul_pred_div_two (ε : Fin n → Bool) : Fintype.card (Qp ε) = n * (n - 1) / 2 := by
  rw [Fintype.card_sum, Fintype.card_subtype, Fintype.card_subtype]
  simp only [ne_eq]
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  have key : ∀ x : Fin n × Fin n,
      ((if ε x.1 = ε x.2 then 1 else 0) + (if ¬ε x.1 = ε x.2 then 1 else 0) : ℕ) = 1 := by
    intro x
    split_ifs <;> simp_all
  simp only [Finset.card_filter (fun x : Fin n × Fin n => ε x.1 = ε x.2),
    Finset.card_filter (fun x : Fin n × Fin n => ¬ε x.1 = ε x.2), ← Finset.sum_add_distrib, key,
    Finset.sum_const, smul_eq_mul, mul_one]
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have h1 : ∀ a : Fin n, (∑ b : Fin n, if b < a then 1 else 0) = (a : ℕ) := by
    intro a
    rw [← Finset.card_filter]
    have : (Finset.univ.filter fun b : Fin n => b < a) = Finset.Iio a := by
      ext b
      simp
    rw [this, Fin.card_Iio]
  simp only [h1]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

/- English proof (translation)
Establish `hsurj : Function.Surjective (idxFun ε)`. Introduce and unpack `⟨a, b⟩`. Break down `lt_trichotomy a b with hab | rfl | hab` into its components or cases. Distinguish the cases in `he : ε b = ε a`. Conclude with `⟨Sum.inr (Sum.inr (Sum.inl ⟨(b, a), hab, he⟩)), rfl⟩`.

Conclude with `⟨Sum.inr (Sum.inr (Sum.inr ⟨(b, a), hab, he⟩)), rfl⟩`. Conclude with `⟨Sum.inl a, rfl⟩`. Distinguish the cases in `he : ε a = ε b`. Conclude with `⟨Sum.inr (Sum.inl (Sum.inl ⟨(a, b), hab, he⟩)), rfl⟩`. Conclude with `⟨Sum.inr (Sum.inl (Sum.inr ⟨(a, b), hab, he⟩)), rfl⟩`.

Establish `hcard : Fintype.card (Fin n ⊕ (Qp ε ⊕ Qp ε)) = Fintype.card (Fin n × Fin n)`. Rewrite using `[Fintype.card_sum, Fintype.card_sum, card_qp_eq_mul_pred_div_two, Fintype.card_prod, Fintype.card_fin]`. Establish `h2 : 2 ∣ n * (n - 1)`. Break down `Nat.even_or_odd n with h | h` into its components or cases. Conclude with `Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _`.

Break down `n with _ | m` into its components or cases. Simplify using the standard rewrite rules. Apply `Dvd.dvd.mul_left` to reduce the goal to its premises. Simplify `h` using `[Nat.odd_add_one, even_iff_two_dvd]`. Take `⟨k, hk⟩` from `h2`.

Rewrite using `[hk, Nat.mul_div_cancel_left _ (by norm_num)]`. Break down `n with _ | m` into its components or cases. Use linear arithmetic over natural numbers and integers. Simplify using `only [Nat.add_sub_cancel] at hk`. Use the polynomial consequences of the given equalities and inequalities.

Conclude with `(Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩`.
-/
theorem idxFun_bij (ε : Fin n → Bool) : Function.Bijective (idxFun ε) := by
  have hsurj : Function.Surjective (idxFun ε) := by
    rintro ⟨a, b⟩
    rcases lt_trichotomy a b with hab | rfl | hab
    · by_cases he : ε b = ε a
      · exact ⟨Sum.inr (Sum.inr (Sum.inl ⟨(b, a), hab, he⟩)), rfl⟩
      · exact ⟨Sum.inr (Sum.inr (Sum.inr ⟨(b, a), hab, he⟩)), rfl⟩
    · exact ⟨Sum.inl a, rfl⟩
    · by_cases he : ε a = ε b
      · exact ⟨Sum.inr (Sum.inl (Sum.inl ⟨(a, b), hab, he⟩)), rfl⟩
      · exact ⟨Sum.inr (Sum.inl (Sum.inr ⟨(a, b), hab, he⟩)), rfl⟩
  have hcard : Fintype.card (Fin n ⊕ (Qp ε ⊕ Qp ε)) = Fintype.card (Fin n × Fin n) := by
    rw [Fintype.card_sum, Fintype.card_sum, card_qp_eq_mul_pred_div_two, Fintype.card_prod, Fintype.card_fin]
    have h2 : 2 ∣ n * (n - 1) := by
      rcases Nat.even_or_odd n with h | h
      · exact Dvd.dvd.mul_right (even_iff_two_dvd.mp h) _
      · rcases n with _ | m
        · simp
        · apply Dvd.dvd.mul_left
          simpa [Nat.odd_add_one, even_iff_two_dvd] using h
    obtain ⟨k, hk⟩ := h2
    rw [hk, Nat.mul_div_cancel_left _ (by norm_num)]
    rcases n with _ | m
    · omega
    · simp only [Nat.add_sub_cancel] at hk
      nlinarith
  exact (Fintype.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcard⟩

def idx (ε : Fin n → Bool) : Fin n ⊕ (Qp ε ⊕ Qp ε) ≃ Fin n × Fin n :=
  Equiv.ofBijective _ (idxFun_bij ε)

/- English proof (translation)
Conclude with `card_qp_eq_mul_pred_div_two ε`.
-/
theorem card_Qp (ε : Fin n → Bool) : Fintype.card (Qp ε) = n * (n - 1) / 2 := by
  exact card_qp_eq_mul_pred_div_two ε

abbrev XC (ε : Fin n → Bool) : Type := (Fin n → ℂ) × (Qp ε → Fin 2 → ℂ)

def Fmap (ε : Fin n → Bool) (st : GCo ε × GCo ε) : XC ε :=
  (fun a => (st.1.1.1 a : ℂ) + (st.2.1.1 a : ℂ) * Complex.I,
   fun q => Sum.elim (fun k => ![st.1.1.2 k, st.2.1.2 k]) (fun p => ![st.1.2 p, st.2.2 p]) q)

/- English proof (translation)
Use `haveI s1 : SigmaFinite (Measure.pi fun _ : KPair ε => (volume : Measure ℂ)) := Measure.pi.sigmaFinite _`. Use `haveI s2 : SigmaFinite (Measure.pi fun _ : PCoord ε => (volume : Measure ℂ)) := Measure.pi.sigmaFinite _`. Use `haveI s3 : SigmaFinite (volume : Measure (KPair ε → ℂ)) := s1`. Use `haveI s4 : SigmaFinite (volume : Measure (PCoord ε → ℂ)) := s2`. Use `haveI s5 : SigmaFinite (Measure.pi fun _ : KPair ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))) := Measure.pi.sigmaFinite _`.

Use `haveI s6 : SigmaFinite (Measure.pi fun _ : PCoord ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))) := Measure.pi.sigmaFinite _`. Establish `U1` using `mp_ppc (volume : Measure (KCo ε)) (volume : Measure (PCoord ε → ℂ)) (volume : Measure (KCo ε)) (volume : Measure (PCoord ε → ℂ))`. Establish `U2` using `(mp_ppc (volume : Measure (Fin n → ℝ)) (volume : Measure (KPair ε → ℂ)) (volume : Measure (Fin n → ℝ)) (volume : Measure (KPair ε → ℂ))).prod (MeasurePreserving.id ((volume : Measure (PCoord ε → ℂ)).prod (volume : Measure (PCoord ε → ℂ))))`. Establish `hC` using `MeasurePreserving.symm Complex.measurableEquivRealProd Complex.volume_preserving_equiv_real_prod`. Establish `hR` using `(measurePreserving_pi (fun _ : Fin n => (volume : Measure ℝ).prod (volume : Measure ℝ)) (fun _ => (volume : Measure ℂ)) (fun _ => hC)).comp (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ …`.

Establish `hF2` using `MeasurePreserving.symm (MeasurableEquiv.piFinTwo (fun _ => ℂ)) (measurePreserving_piFinTwo (fun _ => (volume : Measure ℂ)))`. Establish `hK` using `(measurePreserving_pi (fun _ : KPair ε => (volume : Measure ℂ).prod (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ)) (fun _ => hF2)).comp (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ (KPair ε)) (measurePreserving_arrowProdE …`. Establish `hPp` using `(measurePreserving_pi (fun _ : PCoord ε => (volume : Measure ℂ).prod (volume : Measure ℂ)) (fun _ => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ)) (fun _ => hF2)).comp (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ (PCoord ε)) (measurePreserving_arrowPro …`. Establish `hQ` using `(measurePreserving_sumPiEquivProdPi_symm (fun _ : Qp ε => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))).comp (hK.prod hPp)`. Establish `U3` using `measurePreserving_prodAssoc ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ))) ((volume : Measure (KPair ε → ℂ)).prod (volume : Measure (KPair ε → ℂ))) ((volume : Measure (PCoord ε → ℂ)).prod (volume : Measure (PCoord ε → ℂ)))`.

Establish `h` using `(hR.prod hQ).comp (U3.comp (U2.comp U1))`. Use `h using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals try (with_reducible rfl)`. Apply the tactic sequence `all_goals try rfl`. Use function extensionality and compare the values at `st`.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `a clear U1 U2 U3 hC hR hF2 hK hPp hQ h s1 s2 s3 s4 s5 s6`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.measurableEquivRealProd, Complex.equivRealProd, Fmap] <;> rfl`. Use function extensionality and compare the values at `q`. Apply the tactic sequence `rcases q with k | p <;> funext i <;> fin_cases i <;> rfl`.
-/
theorem mp_Fmap (ε : Fin n → Bool) : MeasurePreserving (Fmap ε) volume volume := by
  haveI s1 : SigmaFinite (Measure.pi fun _ : KPair ε => (volume : Measure ℂ)) :=
    Measure.pi.sigmaFinite _
  haveI s2 : SigmaFinite (Measure.pi fun _ : PCoord ε => (volume : Measure ℂ)) :=
    Measure.pi.sigmaFinite _
  haveI s3 : SigmaFinite (volume : Measure (KPair ε → ℂ)) := s1
  haveI s4 : SigmaFinite (volume : Measure (PCoord ε → ℂ)) := s2
  haveI s5 : SigmaFinite (Measure.pi fun _ : KPair ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))) :=
    Measure.pi.sigmaFinite _
  haveI s6 : SigmaFinite (Measure.pi fun _ : PCoord ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))) :=
    Measure.pi.sigmaFinite _
  have U1 := mp_ppc (volume : Measure (KCo ε)) (volume : Measure (PCoord ε → ℂ))
    (volume : Measure (KCo ε)) (volume : Measure (PCoord ε → ℂ))
  have U2 := (mp_ppc (volume : Measure (Fin n → ℝ)) (volume : Measure (KPair ε → ℂ))
    (volume : Measure (Fin n → ℝ)) (volume : Measure (KPair ε → ℂ))).prod
    (MeasurePreserving.id ((volume : Measure (PCoord ε → ℂ)).prod (volume : Measure (PCoord ε → ℂ))))
  have hC := MeasurePreserving.symm Complex.measurableEquivRealProd
    Complex.volume_preserving_equiv_real_prod
  have hR := (measurePreserving_pi (fun _ : Fin n => (volume : Measure ℝ).prod (volume : Measure ℝ))
    (fun _ => (volume : Measure ℂ)) (fun _ => hC)).comp
    (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) (fun _ => (volume : Measure ℝ))
        (fun _ => (volume : Measure ℝ))))
  have hF2 := MeasurePreserving.symm (MeasurableEquiv.piFinTwo (fun _ => ℂ))
    (measurePreserving_piFinTwo (fun _ => (volume : Measure ℂ)))
  have hK := (measurePreserving_pi (fun _ : KPair ε => (volume : Measure ℂ).prod (volume : Measure ℂ))
    (fun _ => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ)) (fun _ => hF2)).comp
    (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ (KPair ε))
      (measurePreserving_arrowProdEquivProdArrow ℂ ℂ (KPair ε) (fun _ => (volume : Measure ℂ))
        (fun _ => (volume : Measure ℂ))))
  have hPp := (measurePreserving_pi (fun _ : PCoord ε => (volume : Measure ℂ).prod (volume : Measure ℂ))
    (fun _ => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ)) (fun _ => hF2)).comp
    (MeasurePreserving.symm (MeasurableEquiv.arrowProdEquivProdArrow ℂ ℂ (PCoord ε))
      (measurePreserving_arrowProdEquivProdArrow ℂ ℂ (PCoord ε) (fun _ => (volume : Measure ℂ))
        (fun _ => (volume : Measure ℂ))))
  have hQ := (measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Qp ε => Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))).comp (hK.prod hPp)
  have U3 := measurePreserving_prodAssoc
    ((volume : Measure (Fin n → ℝ)).prod (volume : Measure (Fin n → ℝ)))
    ((volume : Measure (KPair ε → ℂ)).prod (volume : Measure (KPair ε → ℂ)))
    ((volume : Measure (PCoord ε → ℂ)).prod (volume : Measure (PCoord ε → ℂ)))
  have h := (hR.prod hQ).comp (U3.comp (U2.comp U1))
  convert h using 1
  all_goals try (with_reducible rfl)
  all_goals try rfl
  funext st
  refine Prod.ext ?_ ?_
  · funext a
    clear U1 U2 U3 hC hR hF2 hK hPp hQ h s1 s2 s3 s4 s5 s6
    apply Complex.ext <;> simp [Complex.measurableEquivRealProd, Complex.equivRealProd, Fmap] <;> rfl
  · funext q
    rcases q with k | p <;> funext i <;> fin_cases i <;> rfl

def H0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, Complex.I; 1, -Complex.I]

def Gl (ε : Fin n → Bool) : XC ε →ₗ[ℝ] XC ε :=
  LinearMap.prodMap (LinearMap.pi fun a => (Algebra.lmul ℝ ℂ Complex.I).comp (LinearMap.proj a))
    (LinearMap.pi fun q => ((Matrix.toLin' H0).restrictScalars ℝ).comp (LinearMap.proj q))

/- English proof (translation)
Unfold `Gl`. Rewrite using `[LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]`. Establish `h1 : LinearMap.det (Algebra.lmul ℝ ℂ Complex.I) = 1`. Rewrite using `[← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_I]`. Establish `h0 : H0.det = -2 * Complex.I`.

Simplify using `[H0, Matrix.det_fin_two_of]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : LinearMap.det ((Matrix.toLin' H0).restrictScalars ℝ) = 4`. Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, h0, Complex.normSq_mul, Complex.normSq_I]`. Evaluate the numerical expressions using `[Complex.normSq_apply]`.

Simplify using `only [h1, h2, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ, card_Qp]`.
-/
theorem det_Gl (ε : Fin n → Bool) : LinearMap.det (Gl ε) = (4 : ℝ) ^ (n * (n - 1) / 2) := by
  unfold Gl
  rw [LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi]
  have h1 : LinearMap.det (Algebra.lmul ℝ ℂ Complex.I) = 1 := by
    rw [← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.normSq_I]
  have h0 : H0.det = -2 * Complex.I := by
    simp [H0, Matrix.det_fin_two_of]
    ring
  have h2 : LinearMap.det ((Matrix.toLin' H0).restrictScalars ℝ) = 4 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, h0,
      Complex.normSq_mul, Complex.normSq_I]
    norm_num [Complex.normSq_apply]
  simp only [h1, h2, Finset.prod_const_one, one_mul, Finset.prod_const, Finset.card_univ, card_Qp]

/- English proof (translation)
Conclude with `Complex.conjLIE.measurePreserving`.
-/
theorem mp_conj : MeasurePreserving (starRingEnd ℂ) volume volume := by
  exact Complex.conjLIE.measurePreserving

def sgc {ε : Fin n → Bool} : Qp ε → ℂ → ℂ
  | Sum.inl _ => fun z => -(starRingEnd ℂ z)
  | Sum.inr _ => fun z => starRingEnd ℂ z

/- English proof (translation)
Consider the cases of `q with`. Consider the case `inl k => exact (LinearIsometryEquiv.neg ℝ (E := ℂ)).measurePreserving.comp mp_conj`. Consider the case `inr p => exact mp_conj`.
-/
theorem mp_sgc {ε : Fin n → Bool} (q : Qp ε) : MeasurePreserving (sgc q) volume volume := by
  cases q with
  | inl k => exact (LinearIsometryEquiv.neg ℝ (E := ℂ)).measurePreserving.comp mp_conj
  | inr p => exact mp_conj

def Avals (ε : Fin n → Bool) (x : XC ε) : Fin n ⊕ (Qp ε ⊕ Qp ε) → ℂ :=
  Sum.elim x.1 (Sum.elim (fun q => x.2 q 0) (fun q => sgc q (x.2 q 1)))

def Amap (ε : Fin n → Bool) (x : XC ε) : Fin n × Fin n → ℂ :=
  MeasurableEquiv.piCongrLeft (fun _ => ℂ) (idx ε) (Avals ε x)

/- English proof (translation)
Establish `hP` using `volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin n => ℂ) (idx ε)`. Establish `hT1` using `measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Qp ε ⊕ Qp ε) => (volume : Measure ℂ))`. Establish `hT2` using `(MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod (measurePreserving_sumPiEquivProdPi_symm (fun _ : Qp ε ⊕ Qp ε => (volume : Measure ℂ)))`. Establish `hT3` using `(MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod ((MeasurePreserving.id (Measure.pi fun _ : Qp ε => (volume : Measure ℂ))).prod (measurePreserving_pi (fun _ : Qp ε => (volume : Measure ℂ)) (fun _ => volume) (fun q => mp_sgc q)))`. Establish `hT4` using `(MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod (measurePreserving_arrowProdEquivProdArrow ℂ ℂ (Qp ε) (fun _ => (volume : Measure ℂ)) (fun _ => (volume : Measure ℂ)))`.

Establish `hT5` using `(MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod (measurePreserving_pi (fun _ : Qp ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ))) (fun _ => (volume : Measure ℂ).prod (volume : Measure ℂ)) (fun _ => measurePreserving_piFinTwo (fun _ => (volume : Measure ℂ))))`. Conclude with `hP.comp (hT1.comp (hT2.comp (hT3.comp (hT4.comp hT5))))`.
-/
theorem mp_Amap (ε : Fin n → Bool) : MeasurePreserving (Amap ε) volume volume := by
  have hP := volume_measurePreserving_piCongrLeft (fun _ : Fin n × Fin n => ℂ) (idx ε)
  have hT1 := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin n ⊕ (Qp ε ⊕ Qp ε) => (volume : Measure ℂ))
  have hT2 := (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Qp ε ⊕ Qp ε => (volume : Measure ℂ)))
  have hT3 := (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod
    ((MeasurePreserving.id (Measure.pi fun _ : Qp ε => (volume : Measure ℂ))).prod
      (measurePreserving_pi (fun _ : Qp ε => (volume : Measure ℂ)) (fun _ => volume)
        (fun q => mp_sgc q)))
  have hT4 := (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod
    (measurePreserving_arrowProdEquivProdArrow ℂ ℂ (Qp ε) (fun _ => (volume : Measure ℂ))
      (fun _ => (volume : Measure ℂ)))
  have hT5 := (MeasurePreserving.id (volume : Measure (Fin n → ℂ))).prod
    (measurePreserving_pi (fun _ : Qp ε => (Measure.pi fun _ : Fin 2 => (volume : Measure ℂ)))
      (fun _ => (volume : Measure ℂ).prod (volume : Measure ℂ))
      (fun _ => measurePreserving_piFinTwo (fun _ => (volume : Measure ℂ))))
  exact hP.comp (hT1.comp (hT2.comp (hT3.comp (hT4.comp hT5))))

def pairMap (ε : Fin n → Bool) (st : GCo ε × GCo ε) : Fin n × Fin n → ℂ :=
  fun ab => gMat st.1 ab.1 ab.2 + Complex.I * gMat st.2 ab.1 ab.2

/- English proof (translation)
Use function extensionality and compare the values at `st ab`. Take `⟨j, rfl⟩` from `(idx ε).surjective ab`. Simplify using `only [Function.comp_apply, Amap, MeasurableEquiv.piCongrLeft_apply_apply]`. Simplify using `only [pairMap, idx, Equiv.ofBijective_apply]`. Break down `j with a | (⟨⟨x, y⟩, h⟩ | ⟨⟨x, y⟩, h⟩) | (⟨⟨x, y⟩, h⟩ | ⟨⟨x, y⟩, h⟩)` into its components or cases.

Use `all_goals`. Simplify using `only [idxFun, Prod.swap_prod_mk, Avals, Sum.elim_inl, Sum.elim_inr, sgc, Gl, Fmap, LinearMap.prodMap_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply, gMat, Matrix.add_apply, kMat, pmat]`. Apply the tactic sequence `all_goals try simp [h.1, h.2, ne_of_gt h.1, (ne_of_gt h.1).symm, not_lt.mpr h.1.le, H0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]`. Apply the tactic sequence `all_goals try simp [H0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]`. Apply the tactic sequence `all_goals try ring_nf`.

Apply the tactic sequence `all_goals try simp`.
-/
theorem pairMap_eq (ε : Fin n → Bool) : pairMap ε = Amap ε ∘ Gl ε ∘ Fmap ε := by
  funext st ab
  obtain ⟨j, rfl⟩ := (idx ε).surjective ab
  simp only [Function.comp_apply, Amap, MeasurableEquiv.piCongrLeft_apply_apply]
  simp only [pairMap, idx, Equiv.ofBijective_apply]
  rcases j with a | (⟨⟨x, y⟩, h⟩ | ⟨⟨x, y⟩, h⟩) | (⟨⟨x, y⟩, h⟩ | ⟨⟨x, y⟩, h⟩)
  all_goals
    simp only [idxFun, Prod.swap_prod_mk, Avals, Sum.elim_inl, Sum.elim_inr, sgc, Gl, Fmap,
      LinearMap.prodMap_apply, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearMap.restrictScalars_apply, Matrix.toLin'_apply, gMat, Matrix.add_apply, kMat, pmat]
  all_goals
    try simp [h.1, h.2, ne_of_gt h.1, (ne_of_gt h.1).symm, not_lt.mpr h.1.le, H0, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Complex.ext_iff]
  all_goals try simp [H0, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Complex.ext_iff]
  all_goals try ring_nf
  all_goals try simp

/- English proof (translation)
Establish `hdet : LinearMap.det (Gl ε) ≠ 0`. Rewrite using `[det_Gl]`. Check the signs of the components of the expression. Establish `hF` using `mp_Fmap ε`. Establish `hA` using `mp_Amap ε`.

Establish `hGm : Measurable (Gl ε)` using `(Gl ε).continuous_of_finiteDimensional.measurable`. Use `haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance`. Use `haveI i2 : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := inferInstance`. Use `haveI i3 : (volume : Measure (Qp ε → Fin 2 → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure (fun _ : Qp ε => (volume : Measure (Fin 2 → ℂ)))`. Use `haveI i4 : (volume : Measure (XC ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℂ)) (volume : Measure (Qp ε → Fin 2 → ℂ))`.

Rewrite using `[pairMap_eq, ← Measure.map_map hA.measurable (hGm.comp hF.measurable), ← Measure.map_map hGm hF.measurable, hF.map_eq, Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul, hA.map_eq, det_Gl]`. Use `congr 2`. Conclude with `abs_of_pos (by positivity)`.
-/
theorem map_pairMap (ε : Fin n → Bool) :
    Measure.map (pairMap ε) volume = ENNReal.ofReal ((4 : ℝ) ^ (n * (n - 1) / 2))⁻¹ • volume := by
  have hdet : LinearMap.det (Gl ε) ≠ 0 := by
    rw [det_Gl]
    positivity
  have hF := mp_Fmap ε
  have hA := mp_Amap ε
  have hGm : Measurable (Gl ε) := (Gl ε).continuous_of_finiteDimensional.measurable
  haveI i1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin 2 → ℂ)).IsAddHaarMeasure := inferInstance
  haveI i3 : (volume : Measure (Qp ε → Fin 2 → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ : Qp ε => (volume : Measure (Fin 2 → ℂ)))
  haveI i4 : (volume : Measure (XC ε)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (Fin n → ℂ))
      (volume : Measure (Qp ε → Fin 2 → ℂ))
  rw [pairMap_eq, ← Measure.map_map hA.measurable (hGm.comp hF.measurable),
    ← Measure.map_map hGm hF.measurable, hF.map_eq,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul, hA.map_eq, det_Gl]
  congr 2
  exact abs_of_pos (by positivity)

end ReciprocityTheory.ChartRestriction.DS.OmegaPQAux
