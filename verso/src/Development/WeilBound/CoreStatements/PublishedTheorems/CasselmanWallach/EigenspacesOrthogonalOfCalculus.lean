import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceOrthogonality

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {ε : Fin n → Bool} {E : Fin n → Fin n → Module.End ℂ V} {A : Module.End ℂ V}

/- English proof (translation)
Unfold `nc`. Rewrite using `[Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]`.
-/
lemma nc_sum (f : Fin n × Fin n → ℂ) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε a ≠ ε b then f (a, b) else 0 := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

/- English proof (translation)
Rewrite using `[Finset.sum_eq_single c]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a _ hac`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations.

Simplify using `[Ne.symm hac]`. Simplify using the standard rewrite rules.
-/
lemma s1 (g : Fin n → Fin n → ℂ) (c : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if c = a then g a b else 0) else 0) =
      ∑ b, if ε c ≠ ε b then g c b else 0 := by
  rw [Finset.sum_eq_single c]
  · refine Finset.sum_congr rfl fun b _ => ?_
    simp
  · intro a _ hac
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [Ne.symm hac]
  · simp

/- English proof (translation)
Rewrite using `[Finset.sum_comm, Finset.sum_eq_single d]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `b _ hbd`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Simplify using `[hbd]`. Simplify using the standard rewrite rules.
-/
lemma s2 (g : Fin n → Fin n → ℂ) (d : Fin n) :
    (∑ a, ∑ b, if ε a ≠ ε b then (if b = d then g a b else 0) else 0) =
      ∑ a, if ε a ≠ ε d then g a d else 0 := by
  rw [Finset.sum_comm, Finset.sum_eq_single d]
  · refine Finset.sum_congr rfl fun a _ => ?_
    simp
  · intro b _ hbd
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hbd]
  · simp

/- English proof (translation)
Establish `h` using `congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h`. Rewrite using `[← sub_eq_iff_eq_add', h]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
lemma comm_apply (hgl : IsGlRep E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d x else 0) - (if d = a then E c b x else 0)) := by
  have h := congrArg (fun T : Module.End ℂ V => T x) (hgl a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
  rw [← sub_eq_iff_eq_add', h]
  split_ifs <;> simp

/- English proof (translation)
Establish `hsgn : adjSign ε c d = 1` using `by simp [adjSign, hcd]`. Establish `h1 : inner ℂ (E c d (E a b x)) (A (E a b y)) = inner ℂ (E a b x) (A (E a b (E d c y))) + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)`. Rewrite using `[huni c d, hsgn, one_mul, ← hA d c hcd.symm, comm_apply hgl d c a b y]`. Rewrite using `[map_add, map_sub, inner_add_right, inner_sub_right]`. Apply the tactic sequence `split_ifs <;> (try simp) <;> ring`.

Rewrite using `[comm_apply hgl a b c d x, inner_add_left, h1, inner_sub_left]`. Apply the tactic sequence `split_ifs <;> (try simp) <;> ring`.
-/
lemma pt (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (a b : Fin n) (x y : V) :
    inner ℂ (E a b (E c d x)) (A (E a b y)) =
      inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0)
      + (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0)
      - (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) := by
  have hsgn : adjSign ε c d = 1 := by simp [adjSign, hcd]
  have h1 : inner ℂ (E c d (E a b x)) (A (E a b y)) = inner ℂ (E a b x) (A (E a b (E d c y)))
      + (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0)
      - (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) := by
    rw [huni c d, hsgn, one_mul, ← hA d c hcd.symm, comm_apply hgl d c a b y]
    rw [map_add, map_sub, inner_add_right, inner_sub_right]
    split_ifs <;> (try simp) <;> ring
  rw [comm_apply hgl a b c d x, inner_add_left, h1, inner_sub_left]
  split_ifs <;> (try simp) <;> ring

/- English proof (translation)
Establish `e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) = (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0) + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0) - (if ε a ≠ ε b then (if b = d then inner ℂ (E a …`. Introduce `a b`. Distinguish the cases in `hab : ε a ≠ ε b`. Simplify using `only [if_pos hab]`. Conclude with `pt hgl huni hA hcd a b x y`.

Simplify using `only [if_neg hab]`. Simplify using the standard rewrite rules. Establish `h1` using `s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c`. Establish `h4` using `s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d`. Establish `h2` using `s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d`.

Establish `h3` using `s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c`. Simplify using `only [beta, nc_sum]`. Simplify using `only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]`. Rewrite using `[h1, h2, h3, h4, hcd]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma key (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z))
    {c d : Fin n} (hcd : ε c = ε d) (x y : V) :
    beta ε E A (E c d x) y = beta ε E A x (E d c y) := by
  have e : ∀ a b, (if ε a ≠ ε b then inner ℂ (E a b (E c d x)) (A (E a b y)) else 0) =
      (if ε a ≠ ε b then inner ℂ (E a b x) (A (E a b (E d c y))) else 0)
      + (if ε a ≠ ε b then (if c = a then inner ℂ (E a b x) (A (E d b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if b = d then inner ℂ (E a b x) (A (E a c y)) else 0) else 0)
      + (if ε a ≠ ε b then (if b = c then inner ℂ (E a d x) (A (E a b y)) else 0) else 0)
      - (if ε a ≠ ε b then (if d = a then inner ℂ (E c b x) (A (E a b y)) else 0) else 0) := by
    intro a b
    by_cases hab : ε a ≠ ε b
    · simp only [if_pos hab]
      exact pt hgl huni hA hcd a b x y
    · simp only [if_neg hab]
      simp
  have h1 := s1 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E d b y))) c
  have h4 := s1 (ε := ε) (fun a b => inner ℂ (E c b x) (A (E a b y))) d
  have h2 := s2 (ε := ε) (fun a b => inner ℂ (E a b x) (A (E a c y))) d
  have h3 := s2 (ε := ε) (fun a b => inner ℂ (E a d x) (A (E a b y))) c
  simp only [beta, nc_sum]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h1, h2, h3, h4, hcd]
  ring

/- English proof (translation)
Simplify using `only [beta, map_sum, sum_inner]`. Conclude with `Finset.sum_comm`.
-/
lemma beta_sum_left {ι : Type*} (s : Finset ι) (f : ι → V) (w : V) :
    beta ε E A (∑ i ∈ s, f i) w = ∑ i ∈ s, beta ε E A (f i) w := by
  simp only [beta, map_sum, sum_inner]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [beta, map_sum, inner_sum]`. Conclude with `Finset.sum_comm`.
-/
lemma beta_sum_right {ι : Type*} (s : Finset ι) (f : ι → V) (v : V) :
    beta ε E A v (∑ i ∈ s, f i) = ∑ i ∈ s, beta ε E A v (f i) := by
  simp only [beta, map_sum, inner_sum]
  exact Finset.sum_comm

/- English proof (translation)
Simplify using `only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_` and prove the remaining obligations. Establish `hab : ε b = ε a` using `(Finset.mem_filter.mp hb).2`. Rewrite using `[key hgl huni hA hab.symm, key hgl huni hA hab]`.
-/
lemma Lsym (hgl : IsGlRep E) (huni : IsInfUnitary ε E)
    (hA : ∀ c d, ε c = ε d → ∀ z, A (E c d z) = E c d (A z)) (v w : V) :
    beta ε E A (casimirK ε E v) w = beta ε E A v (casimirK ε E w) := by
  simp only [casimirK, LinearMap.sum_apply, Module.End.mul_apply, beta_sum_left, beta_sum_right]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
  have hab : ε b = ε a := (Finset.mem_filter.mp hb).2
  rw [key hgl huni hA hab.symm, key hgl huni hA hab]

/- English proof (translation)
Unfold `beta`. Simplify using `[Finset.mul_sum]`.
-/
lemma beta_smul_left (r : ℝ) (v w : V) :
    beta ε E A ((r : ℂ) • v) w = (r : ℂ) * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

/- English proof (translation)
Unfold `beta`. Simplify using `[Finset.mul_sum]`.
-/
lemma beta_smul_right (r : ℂ) (v w : V) :
    beta ε E A v (r • w) = r * beta ε E A v w := by
  unfold beta
  simp [Finset.mul_sum]

end EigenspaceOrthogonality

/- English proof (translation)
Introduce `hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw`. Take `⟨-, -, hZ, -⟩` from `hA0 n ε V E h`. Take `⟨hfc, -⟩` from `hA11b n ε V E h ι b μ hB`. Establish `hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z)`. Introduce `c d hcd z`.

Establish `heig : ∀ i, Eig ε E (μ i) (E c d (b i))`. Introduce `i`. Establish `hz` using `congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)`. Simplify using `only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz`. Use `show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)`.

Rewrite using `[sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]`. Establish `hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ)`. Use `b.ext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]`.

Conclude with `LinearMap.congr_fun hT z`. Establish `hL` using `EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w`. Rewrite `hL` using `[show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv, show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw, EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right]`. Establish `hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0`. Rewrite using `[sub_mul, hL, sub_self]`.

Break down `mul_eq_zero.mp hm with h0 | h0` into its components or cases. Conclude with `absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne`. Conclude with `h0`.
-/
theorem eigenspaces_orthogonal_of_calculus : A0 → FunctionalCalculusLaws → EigenspacesOrthogonalAlt := by
  intro hA0 hA11b n ε V _ _ E h ι b μ hB φ ν ν' v w hne hv hw
  obtain ⟨-, -, hZ, -⟩ := hA0 n ε V E h
  obtain ⟨hfc, -⟩ := hA11b n ε V E h ι b μ hB
  have hcomm : ∀ c d, ε c = ε d → ∀ z, fc b μ φ (E c d z) = E c d (fc b μ φ z) := by
    intro c d hcd z
    have heig : ∀ i, Eig ε E (μ i) (E c d (b i)) := by
      intro i
      have hz := congrArg (fun T : Module.End ℂ V => T (b i)) (hZ c d hcd)
      simp only [Z, LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply] at hz
      show casimirK ε E (E c d (b i)) = ((μ i : ℝ) : ℂ) • E c d (b i)
      rw [sub_eq_zero.mp hz, show casimirK ε E (b i) = ((μ i : ℝ) : ℂ) • b i from hB.eig i, map_smul]
    have hT : (fc b μ φ).comp (E c d) = (E c d).comp (fc b μ φ) := by
      refine b.ext fun i => ?_
      simp only [LinearMap.comp_apply]
      rw [hfc φ (μ i) _ (heig i), hfc φ (μ i) _ (hB.eig i), map_smul]
    exact LinearMap.congr_fun hT z
  have hL := EigenspaceOrthogonality.Lsym (A := fc b μ φ) h.gl h.uni hcomm v w
  rw [show casimirK ε E v = ((ν : ℝ) : ℂ) • v from hv,
    show casimirK ε E w = ((ν' : ℝ) : ℂ) • w from hw,
    EigenspaceOrthogonality.beta_smul_left, EigenspaceOrthogonality.beta_smul_right] at hL
  have hm : (((ν : ℝ) : ℂ) - ((ν' : ℝ) : ℂ)) * beta ε E (fc b μ φ) v w = 0 := by
    rw [sub_mul, hL, sub_self]
  rcases mul_eq_zero.mp hm with h0 | h0
  · exact absurd (Complex.ofReal_injective (sub_eq_zero.mp h0)) hne
  · exact h0

end PositivityTheory.CW

end
