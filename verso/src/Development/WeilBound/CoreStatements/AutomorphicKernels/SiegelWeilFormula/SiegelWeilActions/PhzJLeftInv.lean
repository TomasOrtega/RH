import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.EisLeftInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.MemStabiliserIffFrameLowerBlock

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Act.C1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

/- English proof (translation)
Apply the tactic sequence `rcases u with a | a <;>`. Distinguish the cases in `ha : a = L.i₀`. Use `right`. Simplify using `[ha]`. Take `⟨a', rfl⟩` from `(L.rng a).1 ha left`.

Apply the tactic sequence `first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩`.
-/
theorem range_or (L : LD d) (u : Fin d.n ⊕ Fin d.n) :
    (∃ u', Sum.map L.em L.em u' = u) ∨ u ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases u with a | a <;>
  · by_cases ha : a = L.i₀
    · right; simp [ha]
    · obtain ⟨a', rfl⟩ := (L.rng a).1 ha
      left; first | exact ⟨Sum.inl a', rfl⟩ | exact ⟨Sum.inr a', rfl⟩

/- English proof (translation)
Rewrite using `[ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]`. Rewrite `hp` using `[ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame]`. Use extensionality with `a c`. Simplify using `only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]`. Break down `range_or L (Sum.inr a) with ⟨u', hu'⟩ | hu` into its components or cases.

Break down `range_or L (Sum.inl c) with ⟨v', hv'⟩ | hv` into its components or cases. Break down `u' with a' | a'` into its components or cases. Simplify using `at hu'`. Break down `v' with c' | c'` into its components or cases. Establish `h1` using `congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')`.

Simplify using `only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1`. Simplify using `only [Sum.map_inr, Sum.inr.injEq] at hu'`. Simplify using `only [Sum.map_inl, Sum.inl.injEq] at hv'`. Rewrite using `[← hu', ← hv', h1]`. Conclude with `congrFun (congrFun hp a') c'`.

Simplify using `at hv'`. Rewrite using `[(L.j_out p _ hv (Sum.inr a)).2]`. Simplify using the standard rewrite rules. Rewrite using `[(L.j_out p _ hu (Sum.inl c)).1]`. Simplify using the standard rewrite rules.
-/
theorem j_par (L : LD d) {p : G2 σ L.Y} (hp : p ∈ par2 σ L.Y) : L.j p ∈ par2 σ d.Y := by
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block d.ok.frame]
  rw [ComplexParameterFamilyContinuity.mem_stabiliser_iff_frame_lower_block L.sd.ok.frame] at hp
  ext a c
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  rcases range_or L (Sum.inr a) with ⟨u', hu'⟩ | hu
  · rcases range_or L (Sum.inl c) with ⟨v', hv'⟩ | hv
    · rcases u' with a' | a'
      · simp at hu'
      rcases v' with c' | c'
      · have h1 := congrFun (congrFun (L.j_in p) (Sum.inr a')) (Sum.inl c')
        simp only [Matrix.submatrix_apply, Sum.map_inr, Sum.map_inl] at h1
        simp only [Sum.map_inr, Sum.inr.injEq] at hu'
        simp only [Sum.map_inl, Sum.inl.injEq] at hv'
        rw [← hu', ← hv', h1]
        exact congrFun (congrFun hp a') c'
      · simp at hv'
    · rw [(L.j_out p _ hv (Sum.inr a)).2]
      simp
  · rw [(L.j_out p _ hu (Sum.inl c)).1]
    simp

/- English proof (translation)
Take `⟨g, hg⟩` from `hp`. Establish `hm : mat2 p = incM F g.1` using `(congrArg Units.val hg).symm`. Establish `hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1)`. Rewrite using `[kunf.incM_mul', kunf.incM_mul', ← hm]`. Both sides reduce to the same expression.

Set `M'` to `(L.b⁻¹).1 * g.1 * L.b.1`. Set `M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E` to `fun u v => if hu : ∃ u', Sum.map L.em L.em u' = u then if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v else (1 : Matrix _ _ E) u v`. Use `kunf.rat_of_inFrame (b := d.b) (M := M) ?_` and prove the remaining obligations. Use extensionality with `u v`. Use `show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)`.

Simplify using `only [M]`. Distinguish the cases in `hu : ∃ u', Sum.map L.em L.em u' = u`. Distinguish the cases in `hv : ∃ v', Sum.map L.em L.em v' = v`. Rewrite using `[dif_pos hu, dif_pos hv]`. Establish `h1` using `congrFun (congrFun (L.j_in p) hu.choose) hv.choose`.

Simplify using `only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1`. Rewrite using `[h1, hL]`. Both sides reduce to the same expression. Rewrite using `[dif_pos hu, dif_neg hv]`. Establish `hv'` using `(range_or L v).resolve_left hv`.

Rewrite using `[(L.j_out p _ hv' u).2]`. Simplify using `[Matrix.one_apply, apply_ite]`. Rewrite using `[dif_neg hu]`. Establish `hu'` using `(range_or L u).resolve_left hu`. Rewrite using `[(L.j_out p _ hu' v).1]`.

Simplify using `[Matrix.one_apply, apply_ite]`.
-/
theorem j_rat (L : LD d) {p : G2 σ L.Y} (hp : p ∈ rat2 σ L.Y) : L.j p ∈ rat2 σ d.Y := by
  obtain ⟨g, hg⟩ := hp
  have hm : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  have hL : inFrame L.b p = incM F ((L.b⁻¹).1 * g.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]; rfl
  let M' := (L.b⁻¹).1 * g.1 * L.b.1
  let M : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E := fun u v =>
    if hu : ∃ u', Sum.map L.em L.em u' = u then
      if hv : ∃ v', Sum.map L.em L.em v' = v then M' hu.choose hv.choose else (1 : Matrix _ _ E) u v
    else (1 : Matrix _ _ E) u v
  refine kunf.rat_of_inFrame (b := d.b) (M := M) ?_
  ext u v
  show inFrame d.b (L.j p) u v = inclR (F := F) (AF F) (M u v)
  dsimp only [M]
  by_cases hu : ∃ u', Sum.map L.em L.em u' = u
  · by_cases hv : ∃ v', Sum.map L.em L.em v' = v
    · rw [dif_pos hu, dif_pos hv]
      have h1 := congrFun (congrFun (L.j_in p) hu.choose) hv.choose
      simp only [Matrix.submatrix_apply, hu.choose_spec, hv.choose_spec] at h1
      rw [h1, hL]
      rfl
    · rw [dif_pos hu, dif_neg hv]
      have hv' := (range_or L v).resolve_left hv
      rw [(L.j_out p _ hv' u).2]
      simp [Matrix.one_apply, apply_ite]
  · rw [dif_neg hu]
    have hu' := (range_or L u).resolve_left hu
    rw [(L.j_out p _ hu' v).1]
    simp [Matrix.one_apply, apply_ite]

/- English proof (translation)
Introduce `p hp g`. Use `show phz d f s₁ z (L.j (p * g) * x) = phz d f s₁ z (L.j g * x)`. Rewrite using `[map_mul, mul_assoc]`. Conclude with `phz_leftInv d hf z (L.j p) ⟨j_par L hp.1, j_rat L hp.2⟩ _`.
-/
theorem phz_j_leftInv (L : LD d) {s₁ : ℂ} {f : d.G → ℂ} (hf : IsSec d.K d.χ s₁ f) (z : ℂ) (x : d.G) :
    GlobalTheory.AutomorphicL2Unitary.LeftInv (par2 σ L.Y ⊓ rat2 σ L.Y)
      (fun g : G2 σ L.Y => ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) := by
  intro p hp g
  show phz d f s₁ z (L.j (p * g) * x) = phz d f s₁ z (L.j g * x)
  rw [map_mul, mul_assoc]
  exact phz_leftInv d hf z (L.j p) ⟨j_par L hp.1, j_rat L hp.2⟩ _

end PositivityTheory.SiegelWeilFormula.Act.C1

end
