import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirProjEqOneOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.BZMir.GpExists

section Entries

variable {k : Type} [Field k]

/- English proof (translation)
Use `show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) p q = _`. Simplify using `[GlobalTheory.BZMir.colMat, hq]`.
-/
theorem unip_apply_of_ne_last (n : ℕ) (v : Multiplicative (Fin n → k)) (p q : Fin (n + 1)) (hq : q ≠ Fin.last n) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p q := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) p q = _
  simp [GlobalTheory.BZMir.colMat, hq]

/- English proof (translation)
Use `show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) (Fin.last n) = 1`. Simplify using `[GlobalTheory.BZMir.colMat]`.
-/
theorem unip_apply_last_last (n : ℕ) (v : Multiplicative (Fin n → k)) :
    ((unip k n v : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) (Fin.last n) (Fin.last n) = 1
  simp [GlobalTheory.BZMir.colMat]

end Entries

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]`.
-/
theorem blockIndex_false_val (m j : ℕ) (a : Fin m) : (eGP m j ⟨false, a⟩ : Fin (m + j + 1)).val = a.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

/- English proof (translation)
Use `first`. Consider the case `rfl`. Consider the case `simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]`.
-/
theorem blockIndex_true_val (m j : ℕ) (b : Fin (j + 1)) : (eGP m j ⟨true, b⟩ : Fin (m + j + 1)).val = m + b.val := by
  first
  | rfl
  | simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.stdSum]

end GlobalTheory.CompanionTheory.BZMir.GpExists

namespace GlobalTheory.CompanionTheory.BZMir

open GpExists

/- English proof (translation)
Establish `hu' : (u : GL (Fin (j + 1)) k) ∈ GlobalTheory.BZMir.MirU k j`. Unfold `GlobalTheory.BZMir.MirUin at hu`. Conclude with `Subgroup.mem_subgroupOf.1 hu`. Unfold `GlobalTheory.BZMir.MirU at hu'`. Rewrite `hu'` using `[MonoidHom.mem_range]`.

Take `⟨w, hw⟩` from `hu'`. Use `set v' : Multiplicative (Fin (m + j) → k) := Multiplicative.ofAdd (Fin.append (0 : Fin m → k) (Multiplicative.toAdd w)) with hv'`. Establish `hU : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.MirU k (m + j)`. Unfold `GlobalTheory.BZMir.MirU`. Conclude with `MonoidHom.mem_range.2 ⟨v', rfl⟩`.

Establish `hM : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.Mir k (m + j)` using `GlobalTheory.BZMir.MirU_le_Mir k (m + j) hU`. Establish `hP : (⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩ : GlobalTheory.BZMir.Mir k (m + j)) ∈ GlobalTheory.BZMir.Leib.MirabolicParabolic k m j`. Unfold `GlobalTheory.BZMir.Leib.MirabolicParabolic`. Rewrite using `[Subgroup.mem_comap]`. Use `show GlobalTheory.BZMir.unip k (m + j) v' ∈ _`.

Use `(GlobalTheory.SmGL.mem_parab_two k).2 (fun b a => ?_)` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last]`. Conclude with `Matrix.one_apply_ne (fun h => by simpa using Equiv.injective _ h)`. Conclude with `GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a`. Use `⟨⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩, ?_, ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.BZMir.MirUin`. Conclude with `Subgroup.mem_subgroupOf.2 hU`. Apply `Prod.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a a'`.

Simplify using `only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply]`. Rewrite using `[GlobalTheory.SmGL.leviProj_apply]`. Express the relevant statement in the definitionally equal form `((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _`. Rewrite using `[GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a')]`. Distinguish the cases in `h : a = a'`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)), Units.val_one, Matrix.one_apply_ne h]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Use extensionality with `b b'`. Use `first`. Consider the case `(show ((GlobalTheory.SmGL.leviProj k (GlobalTheory.BZMir.Leib.eGP m j) (GlobalTheory.BZMir.Leib.hgpIncl k m j ⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩) true : GL _ k) : Matrix _ _ k) b b' = _`. Rewrite using `[GlobalTheory.SmGL.leviProj_apply])`. Consider the case `(simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.codRestrict_apply, MonoidHom.coe_codRestrict, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_mk]`.

Rewrite using `[GlobalTheory.SmGL.leviProj_apply])`. Express the relevant statement in the definitionally equal form `((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _`. Rewrite using `[← hw]`. Proceed by induction on `b' using Fin.lastCases with`. Consider the case `last`.

Rewrite using `[GlobalTheory.BZMir.Leib.blockIndex_true_last]`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last`. Rewrite using `[GlobalTheory.BZMir.Leib.blockIndex_true_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last]`. Consider the case `cast i`.

Establish `hidx : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ = Fin.castSucc (Fin.natAdd m i)` using `Fin.ext (by simp [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val])`. Rewrite using `[hidx, GlobalTheory.BZMir.unip_apply_castSucc_last, GlobalTheory.BZMir.unip_apply_castSucc_last, hv']`. Simplify using the standard rewrite rules. Consider the case `cast i`. Establish `hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ ≠ Fin.last (m + j)` using `fun h => Fin.castSucc_ne_last i ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).1 h)`.

Rewrite using `[GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ hne, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last i)]`. Distinguish the cases in `h : b = Fin.castSucc i`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)), Matrix.one_apply_ne h]`.
-/
theorem exists_gpProj_unip (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m j : ℕ) (u : Mir k j) (hu : u ∈ MirUin k j) :
    ∃ v : MirabolicParabolic k m j, (v : Mir k (m + j)) ∈ MirUin k (m + j) ∧ gpProj k m j v = (1, u) := by
  have hu' : (u : GL (Fin (j + 1)) k) ∈ GlobalTheory.BZMir.MirU k j := by
    unfold GlobalTheory.BZMir.MirUin at hu
    exact Subgroup.mem_subgroupOf.1 hu
  unfold GlobalTheory.BZMir.MirU at hu'
  rw [MonoidHom.mem_range] at hu'
  obtain ⟨w, hw⟩ := hu'
  set v' : Multiplicative (Fin (m + j) → k) :=
    Multiplicative.ofAdd (Fin.append (0 : Fin m → k) (Multiplicative.toAdd w)) with hv'
  have hU : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.MirU k (m + j) := by
    unfold GlobalTheory.BZMir.MirU
    exact MonoidHom.mem_range.2 ⟨v', rfl⟩
  have hM : GlobalTheory.BZMir.unip k (m + j) v' ∈ GlobalTheory.BZMir.Mir k (m + j) :=
    GlobalTheory.BZMir.MirU_le_Mir k (m + j) hU
  have hP : (⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩ : GlobalTheory.BZMir.Mir k (m + j)) ∈
      GlobalTheory.BZMir.Leib.MirabolicParabolic k m j := by
    unfold GlobalTheory.BZMir.Leib.MirabolicParabolic
    rw [Subgroup.mem_comap]
    show GlobalTheory.BZMir.unip k (m + j) v' ∈ _
    refine (GlobalTheory.SmGL.mem_parab_two k).2 (fun b a => ?_)
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last]
    · exact Matrix.one_apply_ne (fun h => by simpa using Equiv.injective _ h)
    · exact GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a
  refine ⟨⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩, ?_, ?_⟩
  · unfold GlobalTheory.BZMir.MirUin
    exact Subgroup.mem_subgroupOf.2 hU
  apply Prod.ext
  · apply Units.ext
    ext a a'
    simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.comp_apply,
      Pi.evalMonoidHom_apply]
    rw [GlobalTheory.SmGL.leviProj_apply]
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (GlobalTheory.BZMir.Leib.blockIndex_false_ne_last m j a')]
    by_cases h : a = a'
    · subst h
      simp
    · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
        Units.val_one, Matrix.one_apply_ne h]
  · apply Subtype.ext
    apply Units.ext
    ext b b'
    first
    | (show ((GlobalTheory.SmGL.leviProj k (GlobalTheory.BZMir.Leib.eGP m j)
          (GlobalTheory.BZMir.Leib.hgpIncl k m j ⟨⟨GlobalTheory.BZMir.unip k (m + j) v', hM⟩, hP⟩) true :
          GL _ k) : Matrix _ _ k) b b' = _
       rw [GlobalTheory.SmGL.leviProj_apply])
    | (simp only [GlobalTheory.BZMir.Leib.gpProj, MonoidHom.prod_apply, MonoidHom.codRestrict_apply,
          MonoidHom.coe_codRestrict, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, Subgroup.coe_mk]
       rw [GlobalTheory.SmGL.leviProj_apply])
    change ((GlobalTheory.BZMir.unip k (m + j) v' : GL (Fin (m + j + 1)) k) :
      Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) _ _ = _
    rw [← hw]
    induction b' using Fin.lastCases with
    | last =>
      rw [GlobalTheory.BZMir.Leib.blockIndex_true_last]
      induction b using Fin.lastCases with
      | last =>
        rw [GlobalTheory.BZMir.Leib.blockIndex_true_last, GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last,
          GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_last_last]
      | cast i =>
        have hidx : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ = Fin.castSucc (Fin.natAdd m i) :=
          Fin.ext (by simp [GlobalTheory.CompanionTheory.BZMir.GpExists.blockIndex_true_val])
        rw [hidx, GlobalTheory.BZMir.unip_apply_castSucc_last, GlobalTheory.BZMir.unip_apply_castSucc_last, hv']
        simp
    | cast i =>
      have hne : GlobalTheory.BZMir.Leib.eGP m j ⟨true, Fin.castSucc i⟩ ≠ Fin.last (m + j) :=
        fun h => Fin.castSucc_ne_last i ((GlobalTheory.BZMir.Leib.blockIndex_true_eq_last_iff m j _).1 h)
      rw [GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ hne,
        GlobalTheory.CompanionTheory.BZMir.GpExists.unip_apply_of_ne_last _ _ _ _ (Fin.castSucc_ne_last i)]
      by_cases h : b = Fin.castSucc i
      · subst h
        simp
      · rw [Matrix.one_apply_ne ((GlobalTheory.BZMir.Leib.eGP m j).injective.ne (by simpa using h)),
          Matrix.one_apply_ne h]

end GlobalTheory.CompanionTheory.BZMir

end
