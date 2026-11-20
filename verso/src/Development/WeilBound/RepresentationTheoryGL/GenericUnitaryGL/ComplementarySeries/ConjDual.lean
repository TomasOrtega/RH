import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil

namespace PositivityTheory.RgGu.NR

namespace ConjDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `k _ _ _ _ n V _ _ π hs hi`. Conclude with `GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hs hi`.
-/
theorem irrAdm' : GlobalTheory.Published.IrreducibleAdmissibleGL := by
  intro k _ _ _ _ n V _ _ π hs hi
  exact GlobalTheory.CompanionTheory.SmGLBridge.irreducibleAdmissible k (Fin n) V π hs hi

/- English proof (translation)
Simplify using `only [detChar, absPow, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]`. Rewrite using `[← Complex.ofReal_cpow (GlobalTheory.SmGL.nabs_pos' k _).le, Complex.conj_ofReal]`.
-/
theorem conj_chi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    starRingEnd ℂ ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) =
      ((detChar (Fin n) (absPow k (s : ℂ)) g : ℂˣ) : ℂ) := by
  simp only [detChar, absPow, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_toHomUnits,
    MonoidHom.coe_mk, OneHom.coe_mk]
  rw [← Complex.ofReal_cpow (GlobalTheory.SmGL.nabs_pos' k _).le, Complex.conj_ofReal]

end ConjDual

open ConjDual in
/- English proof (translation)
Introduce `n V _ _ ρ hs hi hu s`. Take `⟨B, -, hBpos, hBinv⟩` from `hu`. Establish `hinv : ∀ (g : GL (Fin n) k) (w : V), ρ g (ρ g⁻¹ w) = w`. Introduce `g w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`.

Set `L : V → Module.Dual ℂ V` to `fun v => { toFun := fun w => B w v map_add' := by intro a b; simp map_smul' := by intro c a; simp }`. Establish `hL : ∀ v w, L v w = B w v` using `fun v w => rfl`. Establish `hmem : ∀ v, L v ∈ smoothPart ρ.dual`. Introduce `v`. Apply `GlobalTheory.SmGL.mem_smoothPart_of_nhds` to reduce the goal to its premises.

Apply `Filter.mem_of_superset ((hs v).mem_nhds (by simp))` to reduce the goal to its premises. Introduce `g hg`. Simplify using `only [Set.mem_setOf_eq] at hg ⊢`. Establish `hv' : ρ g⁻¹ v = v` using `by conv_lhs => rw [← hg]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`.

Use extensionality with `w`. Rewrite using `[Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hL, hL]`. Rewrite using `[← hBinv g⁻¹ w v, hv']`. Set `φ : V →ₗ⋆[ℂ] smoothPart ρ.dual` to `{ toFun := fun v => ⟨L v, hmem v⟩ map_add' := by`. Introduce `a b`.

Use extensionality with `w`. Simplify using `[hL]`. Use the proof step `map_smul' := by`. Introduce `c a`. Use extensionality with `w`.

Simplify using `[hL] }`. Establish `hφ : ∀ v w, (φ v : Module.Dual ℂ V) w = B w v` using `fun v w => rfl`. Establish `hint : ∀ (g : GL (Fin n) k) (v : V), φ (ρ g v) = contra ρ g (φ v)`. Introduce `g v`. Use extensionality with `w`.

Rewrite using `[contra_apply, hφ, hφ, ← hBinv g (ρ g⁻¹ w) v, hinv]`. Use `⟨φ, ⟨?_, ?_⟩, fun g v => ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `v hv`. Assume the negation of the conclusion as `hne`.

Establish `h0` using `hBpos v hne`. Establish `: B v v = 0`. Rewrite using `[← hφ, hv]`. Both sides reduce to the same expression. Rewrite `h0` using `[this]`.

Simplify using `at h0`. Establish `hadm` using `irrAdm' k n V ρ hs hi`. Establish `hbasis : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U`. Introduce `U hU`. Take `⟨J, hJo, hJU, hJK, -⟩` from `GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (Fin n) U hU`.

Conclude with `⟨J, hJo, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) (fun x hx => hJK hx), hJU⟩`. Establish `hci` using `GlobalTheory.ContraRefl.contra_isIrreducible hbasis hadm hi`. Set `S : Subrepresentation (contra ρ)` to `⟨LinearMap.range φ, by`. Introduce and unpack `g x ⟨v, rfl⟩`. Conclude with `⟨ρ g v, hint g v⟩⟩`.

Use `haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hi`. Break down `eq_bot_or_eq_top S with h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨v, hv⟩` from `exists_ne (0 : V)`. Establish `hm : φ v ∈ S.toSubmodule` using `LinearMap.mem_range_self φ v`.

Rewrite `hm` using `[h]`. Establish `hz : φ v = 0` using `(Submodule.mem_bot ℂ).1 hm`. Establish `h0` using `hBpos v hv`. Establish `: B v v = 0`. Rewrite using `[← hφ, hz]`.

Both sides reduce to the same expression. Rewrite `h0` using `[this]`. Simplify using `at h0`. Establish `hr : LinearMap.range φ = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `LinearMap.range_eq_top.1 hr`.

Rewrite using `[twist_apply, twist_apply, map_smulₛₗ, conj_chi, hint]`.
-/
theorem conjDual (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ConjDual k := by
  intro n V _ _ ρ hs hi hu s
  obtain ⟨B, -, hBpos, hBinv⟩ := hu
  have hinv : ∀ (g : GL (Fin n) k) (w : V), ρ g (ρ g⁻¹ w) = w := by
    intro g w
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  let L : V → Module.Dual ℂ V := fun v =>
    { toFun := fun w => B w v
      map_add' := by intro a b; simp
      map_smul' := by intro c a; simp }
  have hL : ∀ v w, L v w = B w v := fun v w => rfl
  have hmem : ∀ v, L v ∈ smoothPart ρ.dual := by
    intro v
    apply GlobalTheory.SmGL.mem_smoothPart_of_nhds
    apply Filter.mem_of_superset ((hs v).mem_nhds (by simp))
    intro g hg
    simp only [Set.mem_setOf_eq] at hg ⊢
    have hv' : ρ g⁻¹ v = v := by
      conv_lhs => rw [← hg]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    ext w
    rw [Representation.dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, hL, hL]
    rw [← hBinv g⁻¹ w v, hv']
  let φ : V →ₗ⋆[ℂ] smoothPart ρ.dual :=
    { toFun := fun v => ⟨L v, hmem v⟩
      map_add' := by
        intro a b
        ext w
        simp [hL]
      map_smul' := by
        intro c a
        ext w
        simp [hL] }
  have hφ : ∀ v w, (φ v : Module.Dual ℂ V) w = B w v := fun v w => rfl
  have hint : ∀ (g : GL (Fin n) k) (v : V), φ (ρ g v) = contra ρ g (φ v) := by
    intro g v
    ext w
    rw [contra_apply, hφ, hφ, ← hBinv g (ρ g⁻¹ w) v, hinv]
  refine ⟨φ, ⟨?_, ?_⟩, fun g v => ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    have h0 := hBpos v hne
    have : B v v = 0 := by
      rw [← hφ, hv]
      rfl
    rw [this] at h0
    simp at h0
  · have hadm := irrAdm' k n V ρ hs hi
    have hbasis : ∀ U ∈ nhds (1 : GL (Fin n) k), ∃ K : Subgroup (GL (Fin n) k),
        IsOpen (K : Set (GL (Fin n) k)) ∧ IsCompact (K : Set (GL (Fin n) k)) ∧ (K : Set (GL (Fin n) k)) ⊆ U := by
      intro U hU
      obtain ⟨J, hJo, hJU, hJK, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset k (Fin n) U hU
      exact ⟨J, hJo, GlobalTheory.SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo)
        (fun x hx => hJK hx), hJU⟩
    have hci := GlobalTheory.ContraRefl.contra_isIrreducible hbasis hadm hi
    let S : Subrepresentation (contra ρ) :=
      ⟨LinearMap.range φ, by
        rintro g x ⟨v, rfl⟩
        exact ⟨ρ g v, hint g v⟩⟩
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible hi
    rcases eq_bot_or_eq_top S with h | h
    · exfalso
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      have hm : φ v ∈ S.toSubmodule := LinearMap.mem_range_self φ v
      rw [h] at hm
      have hz : φ v = 0 := (Submodule.mem_bot ℂ).1 hm
      have h0 := hBpos v hv
      have : B v v = 0 := by
        rw [← hφ, hz]
        rfl
      rw [this] at h0
      simp at h0
    · have hr : LinearMap.range φ = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact LinearMap.range_eq_top.1 hr
  · rw [twist_apply, twist_apply, map_smulₛₗ, conj_chi, hint]

end PositivityTheory.RgGu.NR

end
