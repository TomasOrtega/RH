import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open MvPolynomial

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem z hz => obtain ⟨j, rfl⟩ := hz`. Conclude with `hv j`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [add_div]`.

Conclude with `O.add_mem ha hb`. Consider the case `smul c a _ ha => rw [Algebra.smul_def, mul_div_assoc]`. Conclude with `O.mul_mem (hk c) ha`.
-/
lemma pf_div_mem {k K : Type} [Field k] [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (O : Subring K)
    (hk : ∀ c : k, algebraMap k K c ∈ O) (y : K) (hv : ∀ j, v j / y ∈ O) (x : K)
    (hx : x ∈ Submodule.span k (Set.range v)) : x / y ∈ O := by
  induction hx using Submodule.span_induction with
  | mem z hz => obtain ⟨j, rfl⟩ := hz; exact hv j
  | zero => simp
  | add a b _ _ ha hb => rw [add_div]; exact O.add_mem ha hb
  | smul c a _ ha => rw [Algebra.smul_def, mul_div_assoc]; exact O.mul_mem (hk c) ha

/- English proof (translation)
Establish `hf : Module.Finite K (K × Ω[K⁄k])` using `⟨by rw [← hv]; exact Submodule.fg_span (Set.finite_range _)⟩`. Establish `: Module.Finite K Ω[K⁄k]` using `Module.Finite.of_surjective (LinearMap.snd K K Ω[K⁄k]) LinearMap.snd_surjective`. Use `⟨hf, ?_⟩` and prove the remaining obligations. Rewrite using `[Module.finrank_prod, Module.finrank_self, hd]`. Use linear arithmetic over natural numbers and integers.
-/
lemma pf_finrank {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) :
    Module.Finite K (K × Ω[K⁄k]) ∧ Module.finrank K (K × Ω[K⁄k]) = d + 1 := by
  have hf : Module.Finite K (K × Ω[K⁄k]) := ⟨by rw [← hv]; exact Submodule.fg_span (Set.finite_range _)⟩
  have : Module.Finite K Ω[K⁄k] := Module.Finite.of_surjective (LinearMap.snd K K Ω[K⁄k]) LinearMap.snd_surjective
  refine ⟨hf, ?_⟩
  rw [Module.finrank_prod, Module.finrank_self, hd]; omega

/- English proof (translation)
Take `⟨_, h⟩` from `pf_finrank d hd v hv`. Use `finrank_range_le_card (R := K) (jet k v)` as an intermediate fact. Establish `e` using `congrArg (fun s : Submodule K (K × Ω[K⁄k]) => Module.finrank K s) hv`. Simplify using `only [finrank_top] at e`. Simplify using `only [Set.finrank, Fintype.card_fin] at this`.

Use linear arithmetic over natural numbers and integers.
-/
lemma pf_card {k K : Type} [Field k] [Field K] [Algebra k K] (d : ℕ) (hd : Module.finrank K Ω[K⁄k] = d)
    {n : ℕ} (v : Fin n → K) (hv : Submodule.span K (Set.range (jet k v)) = ⊤) : d + 1 ≤ n := by
  obtain ⟨_, h⟩ := pf_finrank d hd v hv
  have := finrank_range_le_card (R := K) (jet k v)
  have e := congrArg (fun s : Submodule K (K × Ω[K⁄k]) => Module.finrank K s) hv
  simp only [finrank_top] at e
  simp only [Set.finrank, Fintype.card_fin] at this
  omega

/- English proof (translation)
Introduce `k K _ _ _ _ d hd htr n v hv`. Take `⟨m, rfl⟩` from `Nat.exists_eq_add_of_le (pf_card d hd v hv)`. Proceed by induction on `m with`. Consider the case `zero`. Take `⟨hf, hr⟩` from `pf_finrank d hd v hv`.

Use `⟨v, fun i => Submodule.subset_span ⟨i, rfl⟩, hv, linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hr]), ?_⟩` and prove the remaining obligations. Introduce `O _ _ h`. Conclude with `h`. Consider the case `succ m ih`. Take `⟨hf, hr⟩` from `pf_finrank d hd v hv`.

Establish `hdep : ¬ LinearIndependent K (jet k v)`. Introduce `hl`. Use `hl.fintype_card_le_finrank` as an intermediate fact. Simplify using `[hr] at this`. Take `⟨e, F, hF0, hFh, hFv⟩` from `hHom k K d htr (d + 1 + (m + 1)) (by omega) v`.

Take `⟨w', hw'k, hw'sp, hw'O⟩` from `hStep k K (d + 1 + m) v e F hF0 hFh hFv hdep`. Take `⟨w, hwk, hwsp, hwli, hwO⟩` from `ih w' (hw'sp.trans hv)`. Use `⟨w, fun i => ?_, hwsp, hwli, ?_⟩` and prove the remaining obligations. Conclude with `Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hw'k j) (hwk i)`. Introduce `O hO hk h`.

Take `⟨i, hi, hiO⟩` from `hw'O O hO hk h`. Take `⟨l, hl, hlO⟩` from `hwO O hO hk ⟨i, hi, fun j => pf_div_mem v O hk _ hiO _ (hw'k j)⟩`. Use `⟨l, hl, fun j => ?_⟩` and prove the remaining obligations. Establish `: v j / w l = (v j / w' i) * (w' i / w l)` using `by field_simp`. Rewrite using `[this]`.

Conclude with `O.mul_mem (hiO j) (hlO i)`.
-/
theorem Project_of (hStep : Step) (hHom : HomRel) : Project := by
  intro k K _ _ _ _ d hd htr n v hv
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le (pf_card d hd v hv)
  induction m with
  | zero =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    refine ⟨v, fun i => Submodule.subset_span ⟨i, rfl⟩, hv,
      linearIndependent_of_top_le_span_of_card_eq_finrank hv.ge (by simp [hr]), ?_⟩
    intro O _ _ h; exact h
  | succ m ih =>
    obtain ⟨hf, hr⟩ := pf_finrank d hd v hv
    have hdep : ¬ LinearIndependent K (jet k v) := by
      intro hl
      have := hl.fintype_card_le_finrank
      simp [hr] at this
    obtain ⟨e, F, hF0, hFh, hFv⟩ := hHom k K d htr (d + 1 + (m + 1)) (by omega) v
    obtain ⟨w', hw'k, hw'sp, hw'O⟩ := hStep k K (d + 1 + m) v e F hF0 hFh hFv hdep
    obtain ⟨w, hwk, hwsp, hwli, hwO⟩ := ih w' (hw'sp.trans hv)
    refine ⟨w, fun i => ?_, hwsp, hwli, ?_⟩
    · exact Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact hw'k j) (hwk i)
    · intro O hO hk h
      obtain ⟨i, hi, hiO⟩ := hw'O O hO hk h
      obtain ⟨l, hl, hlO⟩ := hwO O hO hk ⟨i, hi, fun j => pf_div_mem v O hk _ hiO _ (hw'k j)⟩
      refine ⟨l, hl, fun j => ?_⟩
      have : v j / w l = (v j / w' i) * (w' i / w l) := by field_simp
      rw [this]; exact O.mul_mem (hiO j) (hlO i)

end LateralTheory.EtaleTrace.Cov
