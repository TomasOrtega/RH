import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEquivEqSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqFinClSumAvg
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMeasDefOfIsTermVol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousAdelicUnitaryEmbedding

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RealType
open GlobalTheory.AutMult (toFin toInf)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopIntegral

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Establish `cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN`. Introduce `i`. Distinguish the cases in `hi : i.val < n`.

Conclude with `Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩`. Use `right`. Apply `Fin.ext` to reduce the goal to its premises. Use `show i.val = n`. Use `i.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use extensionality with `i j`. Apply the tactic sequence `rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl`. Rewrite using `[h1, h1']`. Rewrite using `[(h2 a).1, (h2' a).1]`.

Rewrite using `[(h2 b).2, (h2' b).2]`. Rewrite using `[h3, h3']`.
-/
theorem isBlock_unique {R : Type} [Zero R] {N n : ℕ} {hN : N = n + 1} {A' B' : Matrix (Fin N) (Fin N) R}
    {A : Matrix (Fin n) (Fin n) R} {t : R} (h : GlobalTheory.BranchFormula.IsBlock hN A' A t) (h' : GlobalTheory.BranchFormula.IsBlock hN B' A t) :
    A' = B' := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have cover : ∀ i : Fin N, (∃ a : Fin n, i = Formalism.L2.Col.Br.iC hN a) ∨ i = Formalism.L2.Col.Br.iL hN := by
    intro i
    by_cases hi : i.val < n
    · exact Or.inl ⟨⟨i.val, hi⟩, Fin.ext rfl⟩
    · right
      apply Fin.ext
      show i.val = n
      have := i.isLt
      omega
  ext i j
  rcases cover i with ⟨a, rfl⟩ | rfl <;> rcases cover j with ⟨b, rfl⟩ | rfl
  · rw [h1, h1']
  · rw [(h2 a).1, (h2' a).1]
  · rw [(h2 b).2, (h2' b).2]
  · rw [h3, h3']

/- English proof (translation)
Establish `hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ` using `fun v v' => (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact`. Use `⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩` and prove the remaining obligations. Introduce `v₁ v₂ v'`. Simplify using `only [map_add, add_mul]`. Conclude with `integral_add (hint _ _) (hint _ _)`.

Introduce `c v v'`. Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Expand and normalize the polynomial expressions, which then agree. Introduce `v v₁ v₂`. Simplify using `only [map_add, mul_add]`. Conclude with `integral_add (hint _ _) (hint _ _)`. Introduce `c v v'`.

Simplify using `only [map_smul, smul_eq_mul]`. Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Expand and normalize the polynomial expressions, which then agree.

Introduce `k v v'`. Simplify using `only [LinearMap.mk₂_apply]`. Establish `e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) = (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j)`. Introduce `j`. Simplify using `only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]`.

Repeatedly rewrite using `[e]`. Conclude with `integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹`.
-/
theorem exists_avg_form {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [MeasurableSpace H]
    [BorelSpace H] (κ : Measure H) [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] {A B : Type} [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] (ρ : H →* Module.End ℂ A) (ρ' : H →* Module.End ℂ B) (Λ : Module.Dual ℂ A)
    (Λ' : Module.Dual ℂ B) (hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) :
    ∃ β : A →ₗ[ℂ] B →ₗ[ℂ] ℂ, (∀ v v', β v v' = ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ∧
      ∀ k v v', β (ρ k v) (ρ' k v') = β v v' := by
  have hint : ∀ v v', Integrable (fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')) κ := fun v v' =>
    (hc v v').integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  refine ⟨LinearMap.mk₂ ℂ (fun v v' => ∫ k, Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') ∂κ) ?_ ?_ ?_ ?_, fun v v' => rfl, ?_⟩
  · intro v₁ v₂ v'
    simp only [map_add, add_mul]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro v v₁ v₂
    simp only [map_add, mul_add]
    exact integral_add (hint _ _) (hint _ _)
  · intro c v v'
    simp only [map_smul, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext k
    ring
  · intro k v v'
    simp only [LinearMap.mk₂_apply]
    have e : ∀ j : H, Λ (ρ j⁻¹ (ρ k v)) * Λ' (ρ' j⁻¹ (ρ' k v')) =
        (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) (k⁻¹ * j) := by
      intro j
      simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
    simp_rw [e]
    exact integral_mul_left_eq_self (μ := κ) (fun j => Λ (ρ j⁻¹ v) * Λ' (ρ' j⁻¹ v')) k⁻¹

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {U : Set T}

/- English proof (translation)
Take `⟨s, hs, hrel, hrat⟩` from `GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom`. Use `⟨s, hs, fun h => ?_, hrat⟩` and prove the remaining obligations. Conclude with `((hrel h _).1 ((embRel_iff d h _).2 rfl))`.
-/
theorem exists_orthogonal_summand_embedding_hom {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) :
    ∃ s : GA D A →* GA D B, Continuous s ∧ (∀ h, stabilizerEmbedding d h = s h) ∧ ∀ γ ∈ GQ A, s γ ∈ GQ B := by
  obtain ⟨s, hs, hrel, hrat⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A d.ι d.isom
  refine ⟨s, hs, fun h => ?_, hrat⟩
  exact ((hrel h _).1 ((embRel_iff d h _).2 rfl))

variable (G) in

/- English proof (translation)
Establish `h` using `G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by`. Introduce `j hj`. Use `injection hj with h1 h2`. Use `D.R.two_le_m` as an intermediate fact. Use the proof step `omega)`.

Simplify `h` using `[Node.neg, Node.rank]`.
-/
theorem isV_last : (G.node (.grid D.R.m D.R.m)).IsV (rankV D D.R.m D.R.m) 0 := by
  have h := G.isV (X := .grid D.R.m D.R.m) ⟨le_rfl, le_rfl⟩ (by
    intro j hj
    injection hj with h1 h2
    have := D.R.two_le_m
    omega)
  simpa [Node.neg, Node.rank] using h

variable (G) in

/- English proof (translation)
The claim follows from `GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)`.
-/
theorem isDefinite_last : IsDefiniteSpace (G.V (.grid D.R.m D.R.m)) := GlobalTheory.RowClaim.TermVolDef.isDefiniteSpace_of_isV (isV_last G)

variable (G) in

/- English proof (translation)
Rewrite using `[(isV_last G).rank, rankV, sLen]`. Use `D.R.two_le_m` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_rank_last : 1 ≤ (G.V (.grid D.R.m D.R.m)).rank := by
  rw [(isV_last G).rank, rankV, sLen]
  have := D.R.two_le_m
  nlinarith
/- English proof (translation)
Use `⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.Branching.embGL_apply, dif_pos ⟨a.2, b.2⟩]`. Both sides reduce to the same expression. Rewrite using `[GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.2 (lt_irrefl _)), if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]`. Rewrite using `[GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]`.

Rewrite using `[GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]`.
-/
private theorem isBlock_embGL' {n N : ℕ} (hN : N = n + 1) (g : GL (Fin n) ℂ) :
    GlobalTheory.BranchFormula.IsBlock hN (Formalism.MainNotions.PrimeDegreeVariant.embGL ℂ n N hN.symm g : Matrix (Fin N) (Fin N) ℂ)
      (g : Matrix (Fin n) (Fin n) ℂ) 1 := by
  refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [GlobalTheory.Branching.embGL_apply, dif_pos ⟨a.2, b.2⟩]
    rfl
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.2 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h))]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)),
      if_neg (fun h => (ne_of_lt a.2) (congrArg Fin.val h).symm)]
  · rw [GlobalTheory.Branching.embGL_apply, dif_neg (fun h => absurd h.1 (lt_irrefl _)), if_pos rfl]

variable {θ : InfFam D} (hθ : IsInfFam θ) (N : Std G U)
include hθ

/- English proof (translation)
Establish `hX : DefNode D.R.m (.grid D.R.m D.R.m)` using `⟨le_rfl, rfl⟩`. Establish `hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈ Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ`. Introduce `τ`. Establish `e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose` using `rfl`. Establish `h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) * star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1` using `Matrix.mem_unitaryGroup_iff.mp (u τ).2`.

Rewrite using `[e1, Matrix.mem_unitaryGroup_iff]`. Establish `h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose = (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose`. Use extensionality with `i j`. Simplify using `[Matrix.star_apply]`. Rewrite using `[h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]`.

Take `⟨k, hk⟩` from `GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu`. Use `⟨k, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[GlobalTheory.RealType.rhoAt_apply]`. Use `congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)` and prove the remaining obligations. Establish `hb` using `GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ`.

Rewrite `hb` using `[hk, GlobalTheory.BrUnique.invTrK_invTrK]`. Conclude with `isBlock_unique hb (isBlock_embGL' _ _)`. Rewrite using `[GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]`.
-/
theorem exists_real_point (u : D.what₂.Tau → Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) :
    ∃ k : GinfC (G.V (.grid D.R.m D.R.m)),
      rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k) = rhoK (wt G (.top D.R.m)) (GlobalTheory.BrUnique.diagU G.sp.topDec.rank.symm u) ∧
      rhoAt θ N (.grid D.R.m D.R.m) k = rhoK (wt G (.grid D.R.m D.R.m)) (GlobalTheory.BrUnique.uGL u) := by
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hu : ∀ τ, (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) ∈
      Matrix.unitaryGroup (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ := by
    intro τ
    have e1 : (invTrK (GlobalTheory.BrUnique.uGL u) τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) =
        (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose := rfl
    have h1 : (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) *
        star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ) = 1 :=
      Matrix.mem_unitaryGroup_iff.mp (u τ).2
    rw [e1, Matrix.mem_unitaryGroup_iff]
    have h2 : star (star (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ)).transpose =
        (u τ : Matrix (Fin (G.V (.grid D.R.m D.R.m)).rank) (Fin (G.V (.grid D.R.m D.R.m)).rank) ℂ).transpose := by
      ext i j
      simp [Matrix.star_apply]
    rw [h2, ← Matrix.transpose_mul, h1, Matrix.transpose_one]
  obtain ⟨k, hk⟩ := GlobalTheory.RealType.exists_realAt_eq (hθ := hθ) (N := N) hX (invTrK (GlobalTheory.BrUnique.uGL u)) hu
  refine ⟨k, ?_, ?_⟩
  · rw [GlobalTheory.RealType.rhoAt_apply]
    refine congrArg (rhoK (wt G (.top D.R.m))) (funext fun τ => Units.ext ?_)
    have hb := GlobalTheory.RealType.isBlock_invTrK_realAt hθ N (k : GA D (G.V (.grid D.R.m D.R.m))) τ
    rw [hk, GlobalTheory.BrUnique.invTrK_invTrK] at hb
    exact isBlock_unique hb (isBlock_embGL' _ _)
  · rw [GlobalTheory.RealType.rhoAt_apply, hk, GlobalTheory.BrUnique.invTrK_invTrK]

/- English proof (translation)
Take `⟨s, hs, he, -⟩` from `exists_orthogonal_summand_embedding_hom G.sp.topDec`. Repeatedly rewrite using `[he]`. Conclude with `((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)`.
-/
theorem continuous_integrand (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (v : VV ℂ (wt G (.top D.R.m)))
    (v' : VV ℂ (wt G (.grid D.R.m D.R.m))) : Continuous fun h : GA D (G.V (.grid D.R.m D.R.m)) =>
      Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec h)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) h⁻¹ v') := by
  obtain ⟨s, hs, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  simp_rw [he]
  exact ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ) v).comp hs.inv).mul
    ((GlobalTheory.RealType.continuous_rhoAt (hθ := hθ) (N := N) (Λ := Λ') v').comp continuous_inv)

/- English proof (translation)
Establish `hV` using `isDefinite_last G`. Establish `: CompactSpace (GinfC (G.V (.grid D.R.m D.R.m)))` using `isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)`. Take `⟨s, -, he, -⟩` from `exists_orthogonal_summand_embedding_hom G.sp.topDec`. Set `ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m)))` to `(rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)`. Set `ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))` to `(rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype`.

Establish `e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)), ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))`. Introduce `k`. Simplify using `only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]`. Establish `e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)), ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹`. Introduce `k`.

Simplify using `only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]`. Establish `e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)), ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))` using `fun k => rfl`. Establish `e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)), ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹` using `fun k => rfl`. Establish `hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v')`. Introduce `v v'`.

Repeatedly rewrite using `[e1', e2']`. Conclude with `(continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val`. Take `⟨β, hβ, hinv⟩` from `exists_avg_form κ ρ ρ' Λ Λ' hc`. Take `⟨c, hc'⟩` from `GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by`. Introduce `u v f`.

Take `⟨k, hk1, hk2⟩` from `exists_real_point hθ N u`. Establish `h` using `hinv k v f`. Rewrite `h` using `[e1, e2, hk1, hk2]`. Conclude with `h)`. Use `⟨c, fun v v' => ?_⟩` and prove the remaining obligations.

Establish `h` using `hβ v v'`. Rewrite `h` using `[e1', e2']`. Rewrite using `[← h]`. Conclude with `(DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl`.
-/
theorem real_average (Λ : Module.Dual ℂ (VV ℂ (wt G (.top D.R.m))))
    (Λ' : Module.Dual ℂ (VV ℂ (wt G (.grid D.R.m D.R.m)))) (κ : Measure (GinfC (G.V (.grid D.R.m D.R.m))))
    [κ.IsMulLeftInvariant] [IsFiniteMeasure κ] :
    ∃ c : ℂ, ∀ (v : VV ℂ (wt G (.top D.R.m))) (v' : VV ℂ (wt G (.grid D.R.m D.R.m))),
      ∫ k, Λ (rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec k)⁻¹ v) * Λ' (rhoAt θ N (.grid D.R.m D.R.m) (k : GA D _)⁻¹ v') ∂κ =
        c * brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) v v' := by
  have hV := isDefinite_last G
  have : CompactSpace (GinfC (G.V (.grid D.R.m D.R.m))) :=
    isCompact_iff_compactSpace.mp (Formalism.IndefR.Eqv.isCompact_GinfC hV.1 hV.2)
  obtain ⟨s, -, he, -⟩ := exists_orthogonal_summand_embedding_hom G.sp.topDec
  let ρ : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.top D.R.m))) :=
    (rhoAt θ N (.top D.R.m)).comp (s.comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype)
  let ρ' : GinfC (G.V (.grid D.R.m D.R.m)) →* Module.End ℂ (VV ℂ (wt G (.grid D.R.m D.R.m))) :=
    (rhoAt θ N (.grid D.R.m D.R.m)).comp (GinfC (G.V (.grid D.R.m D.R.m))).subtype
  have e1 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m)))) := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, he]
  have e1' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ k⁻¹ = rhoAt θ N (.top D.R.m) (stabilizerEmbedding G.sp.topDec (k : GA D (G.V (.grid D.R.m D.R.m))))⁻¹ := by
    intro k
    simp only [ρ, MonoidHom.comp_apply, Subgroup.coe_subtype, map_inv, he]
  have e2 : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m))) := fun k => rfl
  have e2' : ∀ k : GinfC (G.V (.grid D.R.m D.R.m)),
      ρ' k⁻¹ = rhoAt θ N (.grid D.R.m D.R.m) (k : GA D (G.V (.grid D.R.m D.R.m)))⁻¹ := fun k => rfl
  have hc : ∀ v v', Continuous fun k => Λ (ρ k⁻¹ v) * Λ' (ρ' k⁻¹ v') := by
    intro v v'
    simp_rw [e1', e2']
    exact (continuous_integrand hθ N Λ Λ' v v').comp continuous_subtype_val
  obtain ⟨β, hβ, hinv⟩ := exists_avg_form κ ρ ρ' Λ Λ' hc
  obtain ⟨c, hc'⟩ := GlobalTheory.BrUnique.brPair_unique G.sp.topDec.rank.symm (one_le_rank_last G)
    (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).1) (fun τ => (GlobalTheory.WtInterlaceC.weights_top_grid G τ).2) β (by
      intro u v f
      obtain ⟨k, hk1, hk2⟩ := exists_real_point hθ N u
      have h := hinv k v f
      rw [e1, e2, hk1, hk2] at h
      exact h)
  refine ⟨c, fun v v' => ?_⟩
  have h := hβ v v'
  simp_rw [e1', e2'] at h
  rw [← h]
  exact (DFunLike.congr_fun (DFunLike.congr_fun hc' v) v').trans rfl

end GlobalTheory.TopIntegral

end
