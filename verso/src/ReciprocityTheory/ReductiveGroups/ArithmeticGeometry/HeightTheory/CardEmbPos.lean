import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HFour
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogNormNonneg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightGeneratorLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntegralLeOfAeLeAffine

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

/- English proof (translation)
Use `haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩`. Conclude with `Fintype.card_pos` after adjusting the coercions.
-/
theorem card_emb_pos : (0 : ℝ) < Fintype.card (K →+* ℂ) := by
  haveI : Nonempty (K →+* ℂ) := ⟨(IsAlgClosed.lift : K →ₐ[ℚ] ℂ).toRingHom⟩
  exact_mod_cast Fintype.card_pos

/- English proof (translation)
Establish `hc : (0 : ℝ) < Fintype.card (K →+* ℂ)` using `card_emb_pos`. Establish `hs : (∑ sg, F sg) ≤ (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.mul_sum]`. Unfold `meanK`.

Rewrite using `[div_le_iff₀ hc]`. Establish `e : ((∑ sg, G sg) / (Fintype.card (K →+* ℂ) : ℝ) + C + r * ((∑ sg, H sg) / (Fintype.card (K →+* ℂ) : ℝ))) * (Fintype.card (K →+* ℂ) : ℝ) = (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg`. Apply the tactic sequence `field_simp <;> ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem meanK_le (F G H : (K →+* ℂ) → ℝ) (C r : ℝ) (hle : ∀ sg, F sg ≤ G sg + C + r * H sg) :
    meanK F ≤ meanK G + C + r * meanK H := by
  have hc : (0 : ℝ) < Fintype.card (K →+* ℂ) := card_emb_pos
  have hs : (∑ sg, F sg) ≤ (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    calc (∑ sg, F sg) ≤ ∑ sg, (G sg + C + r * H sg) := Finset.sum_le_sum (fun sg _ => hle sg)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.mul_sum]
  unfold meanK
  rw [div_le_iff₀ hc]
  have e : ((∑ sg, G sg) / (Fintype.card (K →+* ℂ) : ℝ) + C +
      r * ((∑ sg, H sg) / (Fintype.card (K →+* ℂ) : ℝ))) * (Fintype.card (K →+* ℂ) : ℝ) =
      (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    field_simp <;> ring
  linarith

/- English proof (translation)
Apply `meanK_le` to reduce the goal to its premises. Introduce `sg`. Simplify using `only [Nsg, NsgMM, del, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_le_sum (fun c _ => d.sg_one hd h hI2be f hf c sg)`.
-/
theorem sg_part (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    meanK (d.Nsg d.wL f) ≤ meanK (d.NsgMM f) + d.del * (d.tableLineDegreeFive * d.DF + d.cc * d.tableLineDegreeTwo) +
      d.cc / d.i * meanK (d.Nsg (d.n1 • d.wde) d.et) := by
  apply meanK_le
  intro sg
  simp only [Nsg, NsgMM, del, Nat.cast_sum, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun c _ => d.sg_one hd h hI2be f hf c sg)

/- English proof (translation)
Establish `hA` using `hd.a3' c hf hf0`. Establish `hB : ∀ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}.Finite` using `fun j => hd.a3' c (hd.w_mem j c) j.2`. Use `(hA.union (Set.finite_iUnion hB)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hne⟩`. Assume the negation of the conclusion as `hnot`.

Simplify using `only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and, not_not] at hnot`. Take `⟨h1, h2⟩` from `hnot`. Apply `hne` to reduce the goal to its premises. Establish `e1 : d.ord c v d.wL f = 0` using `h1 hv`. Establish `e2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) = 0` using `fun j => h2 j hv`.

Establish `hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = 0`. Establish `e3 : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0` using `funext e2`. Rewrite using `[show (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = ⨅ _ : {j // d.w j c ≠ 0}, (0 : ℤ) from congrArg iInf e3]`. Break down `isEmpty_or_nonempty {j // d.w j c ≠ 0} with hE | hE` into its components or cases. Rewrite using `[iInf, Set.range_eq_empty, Int.csInf_empty]`.

Conclude with `ciInf_const`. Simplify using `only [ordMM, e1, hinf, sub_zero, Int.cast_zero]`.
-/
theorem ordMM_fin (hd : d.AxH 𝒜) (c : ι) (f : A c) (hf : f ∈ 𝒜 c d.wL) (hf0 : f ≠ 0) :
    {v | d.admitted c v ∧ (d.ordMM c v f : ℝ) ≠ 0}.Finite := by
  have hA := hd.a3' c hf hf0
  have hB : ∀ j : {j // d.w j c ≠ 0}, {v | d.admitted c v ∧ d.ord c v d.wL (d.w j c) ≠ 0}.Finite :=
    fun j => hd.a3' c (hd.w_mem j c) j.2
  refine (hA.union (Set.finite_iUnion hB)).subset ?_
  rintro v ⟨hv, hne⟩
  by_contra hnot
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and,
    not_not] at hnot
  obtain ⟨h1, h2⟩ := hnot
  apply hne
  have e1 : d.ord c v d.wL f = 0 := h1 hv
  have e2 : ∀ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) = 0 := fun j => h2 j hv
  have hinf : (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) = 0 := by
    have e3 : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0 := funext e2
    rw [show (⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c)) =
      ⨅ _ : {j // d.w j c ≠ 0}, (0 : ℤ) from congrArg iInf e3]
    rcases isEmpty_or_nonempty {j // d.w j c ≠ 0} with hE | hE
    · rw [iInf, Set.range_eq_empty, Int.csInf_empty]
    · exact ciInf_const
  simp only [ordMM, e1, hinf, sub_zero, Int.cast_zero]

/- English proof (translation)
Establish `hln : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la` using `fun la => Real.log_natCast_nonneg _`. Establish `finG : ∀ (G : WT) (ta : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (Function.support (fun la => d.NlaG h G ta la * logNorm la)).Finite`. Introduce `G ta hta`. Establish `h1 : (Function.support (d.NlaG h G ta)).Finite`. Use `Set.Finite.subset (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ord c v G (ta c)) (hd.a3' c (hta c).1 (hta c).2)) ?_` and prove the remaining obligations.

Conclude with `d.aNla_supp hd h (fun c v g => d.ord c v G g) ta`. Conclude with `h1.subset (fun x hx => left_ne_zero_of_mul hx)`. Establish `finMM : (Function.support (fun la => d.NlaMM h f la * logNorm la)).Finite`. Establish `h1 : (Function.support (d.NlaMM h f)).Finite`. Use `Set.Finite.subset (Set.finite_iUnion fun c => d.la_fin hd h c (fun v => d.ordMM c v (f c)) ?_) ?_` and prove the remaining obligations.

Use `(d.ordMM_fin hd c (f c) (hf c).1 (hf c).2).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨hv, hne⟩`. Conclude with `⟨hv, Int.cast_ne_zero.mpr hne⟩`. Conclude with `d.aNla_supp hd h (fun c v g => d.ordMM c v g) f`. Conclude with `h1.subset (fun x hx => left_ne_zero_of_mul hx)`.

Establish `finNu : (Function.support (fun la => d.nu la * logNorm la)).Finite` using `hH1.2.1.subset (fun x hx => left_ne_zero_of_mul hx)`. Establish `finL` using `finG d.wL f hf`. Establish `finE` using `finG (d.n1 • d.wde) d.et (fun c => ⟨hd.et_mem c, hd.et_ne c⟩)`. Establish `finAll` using `finMM.union (finNu.union finE)`. Establish `key : ∑ᶠ la, d.NlaG h d.wL f la * logNorm la ≤ ∑ᶠ la, (d.NlaMM h f la * logNorm la + d.del * (d.nu la * logNorm la) + d.cc / d.i * (d.NlaG h (d.n1 • d.wde) d.et la * logNorm la))`.

Use `finsum_le_finsum' finL (finAll.subset fun x hx => ?_) fun la => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at hn`. Apply `hx` to reduce the goal to its premises. Simplify using `[hn.1, hn.2.1, hn.2.2]`.

Use `mul_le_mul_of_nonneg_right (d.Nla_le hd h hH1 f la) (hln la)` as an intermediate fact. Conclude with `this.trans_eq (by ring)`. Use `key.trans_eq ?_` and prove the remaining obligations. Rewrite using `[finsum_add_distrib, finsum_add_distrib, mul_finsum, mul_finsum]`. Use `all_goals`.

Use `finAll.subset fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Simplify using `only [Set.mem_union, Function.mem_support, not_or, not_not] at hn`. Apply `hx` to reduce the goal to its premises. Simplify using `[hn.1, hn.2.1, hn.2.2]`.
-/
theorem la_part (hd : d.AxH 𝒜) (h : d.S1) (hH1 : d.FinitePlaceHyp) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) :
    (∑ᶠ la, d.NlaG h d.wL f la * logNorm la) ≤ (∑ᶠ la, d.NlaMM h f la * logNorm la) +
      d.del * (∑ᶠ la, d.nu la * logNorm la) +
      d.cc / d.i * (∑ᶠ la, d.NlaG h (d.n1 • d.wde) d.et la * logNorm la) := by
  have hln : ∀ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), 0 ≤ logNorm la :=
    fun la => Real.log_natCast_nonneg _

  have finG : ∀ (G : WT) (ta : ∀ c, A c), (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) →
      (Function.support (fun la => d.NlaG h G ta la * logNorm la)).Finite := by
    intro G ta hta
    have h1 : (Function.support (d.NlaG h G ta)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ord c v G (ta c)) (hd.a3' c (hta c).1 (hta c).2)) ?_
      exact d.aNla_supp hd h (fun c v g => d.ord c v G g) ta
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finMM : (Function.support (fun la => d.NlaMM h f la * logNorm la)).Finite := by
    have h1 : (Function.support (d.NlaMM h f)).Finite := by
      refine Set.Finite.subset (Set.finite_iUnion fun c =>
        d.la_fin hd h c (fun v => d.ordMM c v (f c)) ?_) ?_
      · refine (d.ordMM_fin hd c (f c) (hf c).1 (hf c).2).subset ?_
        rintro v ⟨hv, hne⟩
        exact ⟨hv, Int.cast_ne_zero.mpr hne⟩
      · exact d.aNla_supp hd h (fun c v g => d.ordMM c v g) f
    exact h1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finNu : (Function.support (fun la => d.nu la * logNorm la)).Finite :=
    hH1.2.1.subset (fun x hx => left_ne_zero_of_mul hx)
  have finL := finG d.wL f hf
  have finE := finG (d.n1 • d.wde) d.et (fun c => ⟨hd.et_mem c, hd.et_ne c⟩)
  have finAll := finMM.union (finNu.union finE)

  have key : ∑ᶠ la, d.NlaG h d.wL f la * logNorm la ≤
      ∑ᶠ la, (d.NlaMM h f la * logNorm la + d.del * (d.nu la * logNorm la) +
        d.cc / d.i * (d.NlaG h (d.n1 • d.wde) d.et la * logNorm la)) := by
    refine finsum_le_finsum' finL (finAll.subset fun x hx => ?_) fun la => ?_
    · by_contra hn
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
      apply hx
      simp [hn.1, hn.2.1, hn.2.2]
    · have := mul_le_mul_of_nonneg_right (d.Nla_le hd h hH1 f la) (hln la)
      exact this.trans_eq (by ring)
  refine key.trans_eq ?_
  rw [finsum_add_distrib, finsum_add_distrib, mul_finsum, mul_finsum]
  all_goals
    refine finAll.subset fun x hx => ?_
    by_contra hn
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hn
    apply hx
    simp [hn.1, hn.2.1, hn.2.2]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
