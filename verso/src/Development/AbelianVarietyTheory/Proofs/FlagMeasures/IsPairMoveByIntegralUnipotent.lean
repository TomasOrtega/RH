import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardBiUnionLe

noncomputable section

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopC.PairMove

open GlobalTheory.LoopC.FrEqv

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Rewrite the hypotheses and the conclusion using the stated equalities.
-/
theorem aut_mul {n m : S.V ≃ₗ[E] S.V} (hm : IsAutLam S Λ m) (hn : IsAutLam S Λ n) : IsAutLam S Λ (m * n) := by
  refine ⟨Subgroup.mul_mem _ hm.1 hn.1, ?_⟩
  have key : ∀ y, (m * n) y ∈ Λ ↔ y ∈ Λ := fun y => by
    show m (n y) ∈ Λ ↔ y ∈ Λ
    rw [aut_mem_iff hm, aut_mem_iff hn]
  ext x
  rw [mem_gmap, ← key ((m * n).symm x), LinearEquiv.apply_symm_apply]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem aut_symm {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) : IsAutLam S Λ n.symm := by
  refine ⟨Subgroup.inv_mem _ hn.1, ?_⟩
  ext x
  rw [mem_gmap, LinearEquiv.symm_symm, aut_mem_iff hn]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem mem_iff_of_map {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) (x : S.V) : n x ∈ W ↔ x ∈ U := by
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem map_of_mem_iff {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : ∀ x, n x ∈ W ↔ x ∈ U) : U.map (n : S.V →ₗ[E] S.V) = W := by
  ext y
  rw [Submodule.mem_map_equiv, ← h (n.symm y), LinearEquiv.apply_symm_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem map_symm {n : S.V ≃ₗ[E] S.V} {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) : W.map (n.symm : S.V →ₗ[E] S.V) = U := by
  ext y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm]
  exact mem_iff_of_map h y

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem orth_mem {n : S.V ≃ₗ[E] S.V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) {U W : Submodule E S.V}
    (h : U.map (n : S.V →ₗ[E] S.V) = W) {x : S.V} (hx : x ∈ orth S U) : n x ∈ orth S W := by
  have hn' : ∀ a b, S.hT (n a) (n b) = S.hT a b := hn
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro w hw
  rw [← h] at hw
  obtain ⟨u, hu, rfl⟩ := hw
  show S.hT (n u) (n x) = 0
  rw [hn']
  exact hx u hu

/- English proof (translation)
Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem lrep_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ Lrep Λ F) : n x ∈ Lrep Λ G := by
  simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, orth_mem hn.1 h hx.2⟩

/- English proof (translation)
Simplify using the standard rewrite rules. Supply the required witnesses or components.
-/
theorem xlam_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F : LFlag S r T} {G : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) {x : S.V} (hx : x ∈ XLam Λ F) : n x ∈ XLam Λ G := by
  simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem] at hx ⊢
  exact ⟨(aut_mem_iff hn x).2 hx.1, (mem_iff_of_map h x).2 hx.2⟩

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem ngx_mem {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    {x : S.V} (hx : x ∈ NgX Λ g F F') : n x ∈ NgX Λ g G G' := by
  have hΛ : Λ.map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) = Λ := hn.2
  have hle : (NgX Λ g F F').map ((n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)) ≤ NgX Λ g G G' := by
    rw [NgX, NgX, Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'', hΛ]
    refine sup_le_sup (sup_le_sup le_rfl ?_) ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h hy
    · rintro _ ⟨y, hy, rfl⟩
      exact xlam_mem hn h' hy
  exact hle (Submodule.mem_map_of_mem hx)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem ngx_iff {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {F G : LFlag S r T} {F' G' : LFlag S r T'}
    (h : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp G) (h' : (Xsp F').map (n : S.V →ₗ[E] S.V) = Xsp G') (g : ℕ)
    (x : S.V) : n x ∈ NgX Λ g G G' ↔ x ∈ NgX Λ g F F' := by
  constructor
  · intro hx
    have := ngx_mem (aut_symm hn) (map_symm h) (map_symm h') g hx
    rwa [LinearEquiv.symm_apply_apply] at this
  · exact ngx_mem hn h h' g

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem nlam_map {n : S.V ≃ₗ[E] S.V} {F : LFlag S r T} (hn : n ∈ NLam Λ F) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp F := by
  have key : ∀ m ∈ NLam Λ F, ∀ x ∈ Xsp F, m x ∈ Xsp F := by
    intro m hm x hx
    rw [← sub_add_cancel (m x) x]
    exact add_mem (hm.2.2 x (X_le_orth hx)) hx
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact key n hn x hx
  · intro x hx
    exact ⟨n.symm x, key _ (symm_mem_NLam hn) x hx, by simp⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  show Submodule.span E (F.fl.e '' {i | i.1 < r}) = Submodule.span E (Set.range F.fl.e)
  rw [show {i : Fin r | i.1 < r} = Set.univ from Set.eq_univ_of_forall fun i => i.2, Set.image_univ]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_X (F : LFlag S r T) : finrank E (Xsp F) = r := by
  show finrank E (Submodule.span E (Set.range F.fl.e)) = r
  rw [finrank_span_eq_card F.fl.e_indep, Fintype.card_fin]

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem frame_move {n : S.V ≃ₗ[E] S.V} {F A : LFlag S r T} {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}
    (h1 : ∀ a b, b < a → ξ a b = 0) (h2 : ∀ a, ξ a a = 1)
    (h3 : frame A = frameAct (fun a => n (frame F a)) ξ) :
    (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A ∧ n F.fl.z - A.fl.z ∈ Xsp A := by
  have hFe : ∀ i : Fin r, frame F i.castSucc = F.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z i.castSucc = F.fl.e i
    simp
  have hAe : ∀ i : Fin r, frame A i.castSucc = A.fl.e i := fun i => by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z i.castSucc = A.fl.e i
    simp
  have hFz : frame F (Fin.last r) = F.fl.z := by
    show Fin.snoc (α := fun _ => S.V) F.fl.e F.fl.z (Fin.last r) = F.fl.z
    simp
  have hAz : frame A (Fin.last r) = A.fl.z := by
    show Fin.snoc (α := fun _ => S.V) A.fl.e A.fl.z (Fin.last r) = A.fl.z
    simp
  have hmem : ∀ i : Fin r, n (frame F i.castSucc) ∈ (Xsp F).map (n : S.V →ₗ[E] S.V) := fun i =>
    Submodule.mem_map_of_mem (by rw [hFe]; exact Submodule.subset_span ⟨i, rfl⟩)
  have hX : Xsp A ≤ (Xsp F).map (n : S.V →ₗ[E] S.V) := by
    show Submodule.span E (Set.range A.fl.e) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [← hAe j, h3]
    simp only [frameAct, SetLike.mem_coe]
    refine Submodule.sum_mem _ fun a _ => ?_
    by_cases ha : j.castSucc < a
    · rw [h1 a j.castSucc ha]
      simp
    · have hne : a ≠ Fin.last r := by
        rintro rfl
        exact ha (Fin.castSucc_lt_last j)
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hne
      exact Submodule.smul_mem _ _ (hmem i)
  have hF : (Xsp F).map (n : S.V →ₗ[E] S.V) = Xsp A := by
    have : FiniteDimensional E (Xsp F) := FiniteDimensional.span_of_finite E (Set.finite_range _)
    symm
    apply Submodule.eq_of_le_of_finrank_eq hX
    rw [LinearEquiv.finrank_map_eq, finrank_X, finrank_X]
  refine ⟨hF, ?_⟩
  rw [← hAz, h3]
  simp only [frameAct]
  rw [Fin.sum_univ_castSucc, h2 (Fin.last r), hFz]
  have hs : ∑ i : Fin r, ((ξ i.castSucc (Fin.last r) : 𝓞 E) : E) • n (frame F i.castSucc) ∈ Xsp A := by
    rw [← hF]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hmem i)
  have e : ((1 : 𝓞 E) : E) • n F.fl.z = n F.fl.z := by simp
  rw [e, sub_add_eq_sub_sub_swap, sub_self, zero_sub]
  exact neg_mem hs

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Simplify using the standard rewrite rules.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the hypotheses and the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem move {g : ℕ} {F : LFlag S r T} {F' F'' A B : LFlag S r T'} {β n' n'' : S.V ≃ₗ[E] S.V}
    (hp : IsPair Λ F F' F'' β g) (hn' : n' ∈ NLam Λ F) (hn'' : n'' ∈ NLam Λ F)
    (hA : (Xsp F').map (n' : S.V →ₗ[E] S.V) = Xsp A) (zA : n' F'.fl.z - A.fl.z ∈ Xsp A)
    (hB : (Xsp F'').map (n'' : S.V →ₗ[E] S.V) = Xsp B) (zB : n'' F''.fl.z - B.fl.z ∈ Xsp B) :
    IsAutLam S Λ (n'' * β * n'⁻¹) ∧
      (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B ∧
      (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  have hn'A : IsAutLam S Λ n' := hn'.1
  have hn''A : IsAutLam S Λ n'' := hn''.1
  obtain ⟨hβ, hβF, hβz, hι⟩ := hp
  have hγ : ∀ x, (n'' * β * n'⁻¹) x = n'' (β (n'.symm x)) := fun x => rfl
  have hβX : (Xsp F').map (β : S.V →ₗ[E] S.V) = Xsp F'' := by
    have := hβF r
    rwa [xflag_top, xflag_top] at this
  have hAB : (Xsp A).map ((n'' * β * n'⁻¹ : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = Xsp B := by
    apply map_of_mem_iff
    intro x
    rw [hγ, mem_iff_of_map hB, mem_iff_of_map hβX, mem_iff_of_map (map_symm hA)]
  have hFn' : (Xsp F).map (n' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn'
  have hFn'' : (Xsp F).map (n'' : S.V →ₗ[E] S.V) = Xsp F := nlam_map hn''
  refine ⟨aut_mul (aut_mul hn''A hβ) (aut_symm hn'A), hAB, ?_, ?_⟩
  · have e : (n'' * β * n'⁻¹) A.fl.z - B.fl.z =
        (n'' F''.fl.z - B.fl.z) - (n'' * β * n'⁻¹) (n' F'.fl.z - A.fl.z) := by
      simp only [hγ, map_sub, LinearEquiv.symm_apply_apply, hβz]
      abel
    rw [e]
    exact sub_mem zB (by rw [← hAB]; exact Submodule.mem_map_of_mem zA)
  · intro x' hx' l hl
    have hy : n'.symm x' ∈ Lrep Λ F' := lrep_mem (aut_symm hn'A) (map_symm hA) hx'
    have hm : n'.symm l ∈ Lrep Λ F := lrep_mem (aut_symm hn'A) (map_symm hFn') hl
    simp only [Lrep, Submodule.mem_inf, Submodule.restrictScalars_mem] at hl
    have h1 : l - x' ∈ NgX Λ g F A ↔ n'.symm l - n'.symm x' ∈ NgX Λ g F F' := by
      rw [← ngx_iff hn'A hFn' hA g, map_sub, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    have h3 : n'.symm l - β (n'.symm x') ∈ NgX Λ g F F'' ↔
        n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [hγ x', ← ngx_iff hn''A hFn'' hB g, map_sub]
    have hd : l - n'' (n'.symm l) ∈ NgX Λ g F B := by
      obtain ⟨hνA, -, hνo⟩ := mul_mem_NLam (symm_mem_NLam hn') hn''
      have e1 : n'' (n'.symm l) - l ∈ XLam Λ F := by
        simp only [XLam, Submodule.mem_inf, Submodule.restrictScalars_mem]
        exact ⟨sub_mem ((aut_mem_iff hνA l).2 hl.1) hl.1, hνo l hl.2⟩
      have e2 : n'' (n'.symm l) - l ∈ NgX Λ g F B := by
        rw [NgX]
        exact Submodule.mem_sup_left (Submodule.mem_sup_right e1)
      rw [← neg_sub]
      exact neg_mem e2
    have h4 : n'' (n'.symm l) - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B ↔
        l - (n'' * β * n'⁻¹) x' ∈ NgX Λ g F B := by
      rw [show l - (n'' * β * n'⁻¹) x' = (n'' (n'.symm l) - (n'' * β * n'⁻¹) x') + (l - n'' (n'.symm l)) by abel]
      exact (add_mem_cancel_right hd).symm
    exact h1.trans ((hι _ hy _ hm).trans (h3.trans h4))

end Gen

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

A detailed English derivation is pending.
-/
theorem pair_move : ∀ (D : D7) (T T' : D.host.E) (Λ : LatV D) (g : ℕ) (F : Fg D T) (F' F'' A B : Fg D T') (β n' n'' : (hS D).V ≃ₗ[D.host.E] (hS D).V), IsPair Λ F F' F'' β g → n' ∈ NLam Λ F → n'' ∈ NLam Λ F → FrameEqv D n' F' A → FrameEqv D n'' F'' B → IsAutLam (hS D) Λ (n'' * β * n'⁻¹) ∧ (Xsp A).map ((n'' * β * n'⁻¹ : (hS D).V ≃ₗ[D.host.E] (hS D).V) : (hS D).V →ₗ[D.host.E] (hS D).V) = Xsp B ∧ (n'' * β * n'⁻¹) A.fl.z - B.fl.z ∈ Xsp B ∧ IotaCompat Λ F A B (n'' * β * n'⁻¹) g := by
  intro D T T' Λ g F F' F'' A B β n' n'' hp hn' hn'' hA hB
  obtain ⟨ξ, h1, h2, h3⟩ := hA
  obtain ⟨η, k1, k2, k3⟩ := hB
  obtain ⟨a1, a2⟩ := frame_move h1 h2 h3
  obtain ⟨b1, b2⟩ := frame_move k1 k2 k3
  exact move hp hn' hn'' a1 a2 b1 b2

end GlobalTheory.LoopC.PairMove

end
