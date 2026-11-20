import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeTransference.TransferenceKey

open Module
open scoped InnerProductSpace

namespace PI

variable {N : ℕ}

/- English proof (translation)
The claim follows from `Real.sInf_nonneg fun _ ht => ht.1`.
-/
lemma succMin_nonneg (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) : 0 ≤ succMin M i := Real.sInf_nonneg fun _ ht => ht.1

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Take `⟨b, hbS, hbspan, hbli⟩` from `exists_linearIndependent ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}`. Establish `hbfin : b.Finite` using `hbli.setFinite`. Use `letI := hbfin.fintype`.

Establish `hcard` using `finrank_span_set_eq_card hbli`. Rewrite `hcard` using `[hbspan]`. Establish `hle : i ≤ Fintype.card b` using `by rw [← Set.toFinset_card]; omega`. Set `e : Fin i ↪ b` to `(Fin.castLEEmb hle).trans (Fintype.equivFin b).symm.toEmbedding`. Set `v : Fin i → EuclideanSpace ℝ (Fin N)` to `fun j => (e j : EuclideanSpace ℝ (Fin N))`.

Establish `hvli : LinearIndependent ℝ v` using `hbli.comp e e.injective`. Establish `hvS : ∀ j, v j ∈ M ∧ ‖v j‖ < succMin M i` using `fun j => hbS (e j).2`. Establish `hne : (Finset.univ : Finset (Fin i)).Nonempty` using `⟨⟨0, hi⟩, Finset.mem_univ _⟩`. Establish `ht_lt : Finset.univ.sup' hne (fun j => ‖v j‖) < succMin M i` using `(Finset.sup'_lt_iff hne).2 fun j _ => (hvS j).2`. Establish `ht_mem : Finset.univ.sup' hne (fun j => ‖v j‖) ∈ {t : ℝ | 0 ≤ t ∧ ∃ v : Fin i → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}` using `⟨(norm_nonneg _).trans (Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ ⟨0, hi⟩)), v, fun j => (hvS j).1, hvli, fun j => Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)⟩`.

Establish `hinf` using `csInf_le ⟨0, fun t ht => ht.1⟩ ht_mem`. Conclude with `lt_irrefl (succMin M i) (lt_of_le_of_lt hinf ht_lt)`.
-/
lemma finrank_span_lt_succMin (M : Submodule ℤ (EuclideanSpace ℝ (Fin N))) (i : ℕ) (hi : 1 ≤ i) :
    finrank ℝ (Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}) < i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hbS, hbspan, hbli⟩ := exists_linearIndependent ℝ
    {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < succMin M i}
  have hbfin : b.Finite := hbli.setFinite
  letI := hbfin.fintype
  have hcard := finrank_span_set_eq_card hbli
  rw [hbspan] at hcard
  have hle : i ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin i ↪ b := (Fin.castLEEmb hle).trans (Fintype.equivFin b).symm.toEmbedding
  let v : Fin i → EuclideanSpace ℝ (Fin N) := fun j => (e j : EuclideanSpace ℝ (Fin N))
  have hvli : LinearIndependent ℝ v := hbli.comp e e.injective
  have hvS : ∀ j, v j ∈ M ∧ ‖v j‖ < succMin M i := fun j => hbS (e j).2
  have hne : (Finset.univ : Finset (Fin i)).Nonempty := ⟨⟨0, hi⟩, Finset.mem_univ _⟩
  have ht_lt : Finset.univ.sup' hne (fun j => ‖v j‖) < succMin M i :=
    (Finset.sup'_lt_iff hne).2 fun j _ => (hvS j).2
  have ht_mem : Finset.univ.sup' hne (fun j => ‖v j‖) ∈ {t : ℝ | 0 ≤ t ∧
      ∃ v : Fin i → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} :=
    ⟨(norm_nonneg _).trans (Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ ⟨0, hi⟩)),
      v, fun j => (hvS j).1, hvli, fun j => Finset.le_sup' (fun j => ‖v j‖) (Finset.mem_univ j)⟩
  have hinf := csInf_le ⟨0, fun t ht => ht.1⟩ ht_mem
  exact lt_irrefl (succMin M i) (lt_of_le_of_lt hinf ht_lt)

/- English proof (translation)
Introduce `N M hdisc hspan i hi hiN`. Establish `hA0 : 0 ≤ succMin M i` using `succMin_nonneg M i`. Establish `hB0 : 0 ≤ succMin (dualZ M) (N + 1 - i)` using `succMin_nonneg _ _`. Break down `hB0.eq_or_lt with hB | hB` into its components or cases. Rewrite using `[← hB, mul_zero]`.

Check the signs of the components of the expression. Use `haveI : DiscreteTopology M := hdisc`. Use `haveI : IsZLattice ℝ M := ⟨hspan⟩`. Use `set A := succMin M i with hAdef`. Use `set B := succMin (dualZ M) (N + 1 - i) with hBdef`.

Use `set Sd : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := Submodule.span ℝ {y : EuclideanSpace ℝ (Fin N) | y ∈ dualZ M ∧ ‖y‖ < B} with hSddef`. Use `set V' : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < A} with hV'def`. Establish `hSd : finrank ℝ Sd < N + 1 - i` using `finrank_span_lt_succMin (dualZ M) (N + 1 - i) (by omega)`. Establish `hV' : finrank ℝ V' < i` using `finrank_span_lt_succMin M i hi`. Establish `hE : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N` using `finrank_euclideanSpace_fin`.

Establish `h1 : finrank ℝ Sd + finrank ℝ Sdᗮ = N` using `(Submodule.finrank_add_finrank_orthogonal Sd).trans hE`. Establish `h2 : finrank ℝ V' + finrank ℝ V'ᗮ = N` using `(Submodule.finrank_add_finrank_orthogonal V').trans hE`. Establish `h3` using `Submodule.finrank_sup_add_finrank_inf_eq Sdᗮ V'ᗮ`. Establish `h4 : finrank ℝ (Sdᗮ ⊔ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≤ N` using `(Submodule.finrank_le _).trans hE.le`. Establish `hne : (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≠ ⊥`.

Introduce `h0`. Rewrite `h3` using `[h0, finrank_bot]`. Use linear arithmetic over natural numbers and integers. Take `⟨u0, hu0W, hu0ne⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Establish `hu0pos : 0 < ‖u0‖` using `norm_pos_iff.2 hu0ne`.

Establish `hN1 : (1 : ℝ) ≤ N` using `by exact_mod_cast (by omega : 1 ≤ N)`. It suffices to establish `hAB : A ≤ N / B by rwa [le_div_iff₀ hB] at hAB`. Apply `le_of_forall_pos_le_add` to reduce the goal to its premises. Introduce `ε hε`. Use `set c : ℝ := N / (2 * B) + ε / 2 with hcdef`.

Establish `hc : 0 < c` using `by positivity`. Use `set u : EuclideanSpace ℝ (Fin N) := (c / ‖u0‖) • u0 with hudef`. Establish `hun : ‖u‖ = c`. Rewrite using `[hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hu0pos), div_mul_cancel₀ _ hu0pos.ne']`. Establish `huW : u ∈ (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N)))` using `Submodule.smul_mem _ _ hu0W`.

Establish `huSd : u ∈ Sdᗮ` using `(Submodule.mem_inf.1 huW).1`. Establish `huV : u ∈ V'ᗮ` using `(Submodule.mem_inf.1 huW).2`. Take `⟨l, hlM, hl⟩` from `h (EuclideanSpace ℝ (Fin N)) M B u hB (fun y hy hyB => by`. Establish `hyd : y ∈ dualZ M` using `fun x hx => by`. Take `⟨n, hn⟩` from `hy x hx`.

Conclude with `⟨n, by rw [real_inner_comm]; exact hn⟩`. Establish `hySd : y ∈ Sd` using `Submodule.subset_span ⟨hyd, hyB⟩`. Conclude with `⟨0, by rw [Submodule.inner_left_of_mem_orthogonal hySd huSd]; simp⟩)`. Rewrite `hl` using `[hE]`. Establish `hul : ‖u - l‖ ≤ N / (2 * B)`.

Rewrite using `[le_div_iff₀ (by positivity)]; linarith`. Establish `hlV : l ∉ V'`. Introduce `hlV`. Establish `hin : inner ℝ u l = 0` using `Submodule.inner_left_of_mem_orthogonal hlV huV`. Establish `hsq : ‖u - l‖ ^ 2 = ‖u‖ ^ 2 + ‖l‖ ^ 2`.

Rewrite using `[@norm_sub_sq_real, hin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hsq2 : ‖u‖ ^ 2 ≤ ‖u - l‖ ^ 2` using `by rw [hsq]; nlinarith [sq_nonneg ‖l‖]`. Establish `hge : ‖u‖ ≤ ‖u - l‖` using `by nlinarith [norm_nonneg (u - l), norm_nonneg u]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hlA : A ≤ ‖l‖`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Conclude with `hlV (Submodule.subset_span ⟨hlM, hlt⟩)`. Establish `htri : ‖l‖ ≤ ‖u‖ + ‖u - l‖`.

Combine the equalities or inequalities in the displayed calculation. Establish `hhalf : (N : ℝ) / (2 * B) + N / (2 * B) = N / B` using `by field_simp; ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem minima_of_key (h : TransferenceKey) : TransferenceMinima := by
  intro N M hdisc hspan i hi hiN
  have hA0 : 0 ≤ succMin M i := succMin_nonneg M i
  have hB0 : 0 ≤ succMin (dualZ M) (N + 1 - i) := succMin_nonneg _ _
  rcases hB0.eq_or_lt with hB | hB
  · rw [← hB, mul_zero]; positivity
  haveI : DiscreteTopology M := hdisc
  haveI : IsZLattice ℝ M := ⟨hspan⟩
  set A := succMin M i with hAdef
  set B := succMin (dualZ M) (N + 1 - i) with hBdef
  set Sd : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.span ℝ {y : EuclideanSpace ℝ (Fin N) | y ∈ dualZ M ∧ ‖y‖ < B} with hSddef
  set V' : Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
    Submodule.span ℝ {x : EuclideanSpace ℝ (Fin N) | x ∈ M ∧ ‖x‖ < A} with hV'def
  have hSd : finrank ℝ Sd < N + 1 - i := finrank_span_lt_succMin (dualZ M) (N + 1 - i) (by omega)
  have hV' : finrank ℝ V' < i := finrank_span_lt_succMin M i hi
  have hE : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  have h1 : finrank ℝ Sd + finrank ℝ Sdᗮ = N := (Submodule.finrank_add_finrank_orthogonal Sd).trans hE
  have h2 : finrank ℝ V' + finrank ℝ V'ᗮ = N := (Submodule.finrank_add_finrank_orthogonal V').trans hE
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Sdᗮ V'ᗮ
  have h4 : finrank ℝ (Sdᗮ ⊔ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≤ N := (Submodule.finrank_le _).trans hE.le
  have hne : (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) ≠ ⊥ := by
    intro h0
    rw [h0, finrank_bot] at h3
    omega
  obtain ⟨u0, hu0W, hu0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hu0pos : 0 < ‖u0‖ := norm_pos_iff.2 hu0ne
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  suffices hAB : A ≤ N / B by rwa [le_div_iff₀ hB] at hAB
  apply le_of_forall_pos_le_add
  intro ε hε
  set c : ℝ := N / (2 * B) + ε / 2 with hcdef
  have hc : 0 < c := by positivity
  set u : EuclideanSpace ℝ (Fin N) := (c / ‖u0‖) • u0 with hudef
  have hun : ‖u‖ = c := by
    rw [hudef, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hc hu0pos), div_mul_cancel₀ _ hu0pos.ne']
  have huW : u ∈ (Sdᗮ ⊓ V'ᗮ : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :=
    Submodule.smul_mem _ _ hu0W
  have huSd : u ∈ Sdᗮ := (Submodule.mem_inf.1 huW).1
  have huV : u ∈ V'ᗮ := (Submodule.mem_inf.1 huW).2
  obtain ⟨l, hlM, hl⟩ := h (EuclideanSpace ℝ (Fin N)) M B u hB (fun y hy hyB => by
    have hyd : y ∈ dualZ M := fun x hx => by
      obtain ⟨n, hn⟩ := hy x hx
      exact ⟨n, by rw [real_inner_comm]; exact hn⟩
    have hySd : y ∈ Sd := Submodule.subset_span ⟨hyd, hyB⟩
    exact ⟨0, by rw [Submodule.inner_left_of_mem_orthogonal hySd huSd]; simp⟩)
  rw [hE] at hl
  have hul : ‖u - l‖ ≤ N / (2 * B) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hlV : l ∉ V' := by
    intro hlV
    have hin : inner ℝ u l = 0 := Submodule.inner_left_of_mem_orthogonal hlV huV
    have hsq : ‖u - l‖ ^ 2 = ‖u‖ ^ 2 + ‖l‖ ^ 2 := by
      rw [@norm_sub_sq_real, hin]; ring
    have hsq2 : ‖u‖ ^ 2 ≤ ‖u - l‖ ^ 2 := by rw [hsq]; nlinarith [sq_nonneg ‖l‖]
    have hge : ‖u‖ ≤ ‖u - l‖ := by nlinarith [norm_nonneg (u - l), norm_nonneg u]
    linarith
  have hlA : A ≤ ‖l‖ := by
    by_contra hlt
    push_neg at hlt
    exact hlV (Submodule.subset_span ⟨hlM, hlt⟩)
  have htri : ‖l‖ ≤ ‖u‖ + ‖u - l‖ := by
    calc ‖l‖ = ‖u - (u - l)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖u‖ + ‖u - l‖ := norm_sub_le _ _
  have hhalf : (N : ℝ) / (2 * B) + N / (2 * B) = N / B := by field_simp; ring
  linarith

end PI
