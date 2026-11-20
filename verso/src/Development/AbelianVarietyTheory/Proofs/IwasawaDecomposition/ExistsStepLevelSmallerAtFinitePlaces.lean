import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
import Formalism.LocalToGlobal.Columns.RecLevelTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TopCh GlobalTheory.Mem.ColAd Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StepLevelShrink

/- English proof (translation)
Use `haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)`. Establish `hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H)` using `Subgroup.isClosed_of_isOpen _ hA`. Establish `hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H)`. Rewrite using `[Subtype.isCompact_iff]`. Use `hU using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`.

Conclude with `⟨⟨x, hUH hx⟩, hx, rfl⟩`. Establish `h2` using `hU'.inter_right hcl`. Rewrite `h2` using `[Subtype.isCompact_iff]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Conclude with `⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩`. Introduce and unpack `⟨y, ⟨_, hy⟩, rfl⟩`. Conclude with `hy`.
-/
theorem isCompact_of_isOpen_subgroupOf {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    (H U A : Subgroup G) (hAU : A ≤ U) (hUH : U ≤ H) (hU : IsCompact (U : Set G))
    (hA : IsOpen {x : H | (x : G) ∈ A}) : IsCompact (A : Set G) := by
  haveI : ContinuousMul H := inferInstanceAs (ContinuousMul H.toSubmonoid)
  have hcl : IsClosed ((A.subgroupOf H : Subgroup H) : Set H) := Subgroup.isClosed_of_isOpen _ hA
  have hU' : IsCompact (Subtype.val ⁻¹' (U : Set G) : Set H) := by
    rw [Subtype.isCompact_iff]
    convert hU using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hUH hx⟩, hx, rfl⟩
  have h2 := hU'.inter_right hcl
  rw [Subtype.isCompact_iff] at h2
  convert h2 using 1
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, hUH (hAU hx)⟩, ⟨hAU hx, hx⟩, rfl⟩
  · rintro ⟨y, ⟨_, hy⟩, rfl⟩
    exact hy

end GlobalTheory.StepLevelShrink

namespace GlobalTheory.StepLevelShrink

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ`. Establish `hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E` using `E) v) y ∈ S.Uloc v := fun y hy => (S.U_eq y).1 hy`. Set `L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F))))` to `{ Lb := S.Lb Lb_fin := S.Lb_fin Lb_span := S.Lb_span Lb_int := S.Lb_int Lb_dual := S.Lb_dual Lb_index := S.Lb_index Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v Uloc_le := by`. Introduce `v`. Distinguish the cases in `hq : v ∈ Qv`.

Rewrite using `[if_pos hq]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`. Conclude with `S.Uloc_le v ((hSU y (hAU hy)).2 v)`. Rewrite using `[if_neg hq]`. Conclude with `S.Uloc_le v`.

Use `Uloc_lev := by`. Introduce `v`. Distinguish the cases in `hq : v ∈ Qv`. Rewrite using `[if_pos hq]`. Introduce and unpack `_ ⟨y, hy, rfl⟩`.

Conclude with `S.Uloc_lev v ((hSU y (hAU hy)).2 v)`. Rewrite using `[if_neg hq]`. Conclude with `S.Uloc_lev v`. Use `Uloc_hyp := by`. Introduce `v hv hT`.

Establish `hb : v ∉ bad` using `fun h => hv (Or.inl h)`. Establish `hq : v ∉ Qv` using `fun h => hv (Or.inr (Finset.mem_coe.2 h))`. Simplify using `only [if_neg hq]`. Conclude with `S.Uloc_hyp v hb hT`. Use `fM := S.fM`.

Use `fM_acg := S.fM_acg`. Use `fM_mod := S.fM_mod`. Use `fT := S.fT`. Use `fT_ne := S.fT_ne`. Use `fT_T := S.fT_T`.

Use `fM_card := S.fM_card`. Use `fT_L := S.fT_L`. Use `UlocAlt := by`. Introduce `v h`. Establish `hq : v ∉ Qv` using `fun hq => hQT v hq h`.

Simplify using `only [if_neg hq]`. Conclude with `S.UlocAlt v h`. Use `U := A`. Use `U_eq := by`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨(hSU x (hAU hx)).1, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hq : v ∈ Qv`. Simplify using `only [if_pos hq]`.

Conclude with `⟨x, hx, rfl⟩`. Simplify using `only [if_neg hq]`. Conclude with `(hSU x (hAU hx)).2 v`. Introduce and unpack `⟨hP, hv⟩`. Establish `hxS : x ∈ S.U`.

Use `(S.U_eq x).2 ⟨hP, fun v => ?_⟩` and prove the remaining obligations. Establish `h1` using `hv v`. Distinguish the cases in `hq : v ∈ Qv`. Simplify using `only [if_pos hq] at h1`. Take `⟨y, hy, hyx⟩` from `h1`.

Rewrite using `[← hyx]`. Conclude with `(hSU y (hAU hy)).2 v`. Simplify using `only [if_neg hq] at h1`. Conclude with `h1`. Use `hloc x hxS fun v hq => ?_` and prove the remaining obligations.

Establish `h1` using `hv v`. Simplify using `only [if_pos hq] at h1`. Take `⟨y, hy, hyx⟩` from `h1`. Conclude with `⟨y, hy, hyx.symm⟩`. Use `U_compact := by`.

Use `letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)`. Use `haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)`. Conclude with `isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU (fun y hy => (hSU y hy).1) S.U_compact hopen`. Use `U_open := hopen`. Use `chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ`.

Use `chi_triv := by`. Introduce `x hx`. Rewrite using `[MonoidHom.mul_apply, MonoidHom.comp_apply, S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)), hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }`. Use `⟨L, rfl, rfl, fun v hv => by show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v` and prove the remaining obligations. Conclude with `if_neg hv, ?_⟩`.

Introduce `x x' x'' h1 h2`. Use `show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''`. Establish `e1 : Subgroup.inclusion hAU x = x'` using `Subtype.ext h1`. Establish `e2 : x = x''` using `Subtype.ext h2`. Rewrite using `[e1, e2]`.
-/
theorem exists_stepLevel_shrink : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (Qv : Finset (HeightOneSpectrum (𝓞 F))) (A : Subgroup (GL (Fin n) (AfE F E))) (ψ : A →* ℂˣ), A ≤ S.U → (∀ v ∈ Qv, (T : 𝓞 F) ∉ v.asIdeal) → (∀ x ∈ S.U, (∀ v ∈ Qv, ∃ x' ∈ A, bc (prV (E := E) v) x = bc (prV (E := E) v) x') → x ∈ A) → (letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); IsOpen {x : UPts σ J (FiniteAdeleRing (𝓞 F) F) | (x : GL _ _) ∈ A}) → (∀ x : A, (∀ v ∈ Qv, bc (prV (E := E) v) x.1 = 1) → ψ x = 1) → ∃ L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))), L.Lb = S.Lb ∧ L.U = A ∧ (∀ v, v ∉ Qv → L.Uloc v = S.Uloc v) ∧ ∀ (x : L.U) (x' : S.U) (x'' : A), x.1 = x'.1 → x.1 = x''.1 → L.chi x = S.chi x' * ψ x'' := by
  intro F E _ _ _ _ _ σ n J T f bad S Qv A ψ hAU hQT hloc hopen hψ
  classical
  have hSU : ∀ y ∈ S.U, y ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F) ∧ ∀ v, bc (prV (E := E) v) y ∈ S.Uloc v :=
    fun y hy => (S.U_eq y).1 hy
  let L : StepLevel F E σ J T f (bad ∪ (Qv : Set (HeightOneSpectrum (𝓞 F)))) :=
    { Lb := S.Lb
      Lb_fin := S.Lb_fin
      Lb_span := S.Lb_span
      Lb_int := S.Lb_int
      Lb_dual := S.Lb_dual
      Lb_index := S.Lb_index
      Uloc := fun v => if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v
      Uloc_le := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_le v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_le v
      Uloc_lev := by
        intro v
        by_cases hq : v ∈ Qv
        · rw [if_pos hq]
          rintro _ ⟨y, hy, rfl⟩
          exact S.Uloc_lev v ((hSU y (hAU hy)).2 v)
        · rw [if_neg hq]
          exact S.Uloc_lev v
      Uloc_hyp := by
        intro v hv hT
        have hb : v ∉ bad := fun h => hv (Or.inl h)
        have hq : v ∉ Qv := fun h => hv (Or.inr (Finset.mem_coe.2 h))
        simp only [if_neg hq]
        exact S.Uloc_hyp v hb hT
      fM := S.fM
      fM_acg := S.fM_acg
      fM_mod := S.fM_mod
      fT := S.fT
      fT_ne := S.fT_ne
      fT_T := S.fT_T
      fM_card := S.fM_card
      fT_L := S.fT_L
      UlocAlt := by
        intro v h
        have hq : v ∉ Qv := fun hq => hQT v hq h
        simp only [if_neg hq]
        exact S.UlocAlt v h
      U := A
      U_eq := by
        intro x
        constructor
        · intro hx
          refine ⟨(hSU x (hAU hx)).1, fun v => ?_⟩
          by_cases hq : v ∈ Qv
          · simp only [if_pos hq]
            exact ⟨x, hx, rfl⟩
          · simp only [if_neg hq]
            exact (hSU x (hAU hx)).2 v
        · rintro ⟨hP, hv⟩
          have hxS : x ∈ S.U := by
            refine (S.U_eq x).2 ⟨hP, fun v => ?_⟩
            have h1 := hv v
            by_cases hq : v ∈ Qv
            · simp only [if_pos hq] at h1
              obtain ⟨y, hy, hyx⟩ := h1
              rw [← hyx]
              exact (hSU y (hAU hy)).2 v
            · simp only [if_neg hq] at h1
              exact h1
          refine hloc x hxS fun v hq => ?_
          have h1 := hv v
          simp only [if_pos hq] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          exact ⟨y, hy, hyx.symm⟩
      U_compact := by
        letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
        haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
        exact isCompact_of_isOpen_subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)) S.U A hAU
          (fun y hy => (hSU y hy).1) S.U_compact hopen
      U_open := hopen
      chi := (S.chi.comp (Subgroup.inclusion hAU)) * ψ
      chi_triv := by
        intro x hx
        rw [MonoidHom.mul_apply, MonoidHom.comp_apply,
          S.chi_triv (Subgroup.inclusion hAU x) (fun v hv => hx v (Or.inl hv)),
          hψ x (fun v hv => hx v (Or.inr (Finset.mem_coe.2 hv))), one_mul] }
  refine ⟨L, rfl, rfl, fun v hv => by
    show (if v ∈ Qv then A.map (bc (prV (E := E) v)) else S.Uloc v) = S.Uloc v
    exact if_neg hv, ?_⟩
  intro x x' x'' h1 h2
  show S.chi (Subgroup.inclusion hAU x) * ψ x = S.chi x' * ψ x''
  have e1 : Subgroup.inclusion hAU x = x' := Subtype.ext h1
  have e2 : x = x'' := Subtype.ext h2
  rw [e1, e2]

end GlobalTheory.StepLevelShrink
