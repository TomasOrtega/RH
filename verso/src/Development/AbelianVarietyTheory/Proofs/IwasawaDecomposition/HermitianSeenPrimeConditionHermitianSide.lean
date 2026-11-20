import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Formalism.LocalToGlobal.UnitaryNorms.UnramT
import Formalism.LocalToGlobal.Columns.DecoFin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt

variable {D : D7} {u : D.what₂.Word}

/- English proof (translation)
Establish `hF : (z : D.host.E) ∈ D.host.F` using `(D.host.conjE_mem_hostF_iff _).2 hz`. Use `⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `(isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp (RingOfIntegers.isIntegral_coe z)`. Both sides reduce to the same expression.
-/
theorem exists_intF_of_conj_eq (z : 𝓞 D.host.E) (hz : D.host.conj (z : D.host.E) = z) :
    ∃ zF : 𝓞 D.host.F, algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF = z := by
  have hF : (z : D.host.E) ∈ D.host.F := (D.host.conjE_mem_hostF_iff _).2 hz
  refine ⟨⟨⟨z, hF⟩, ?_⟩, ?_⟩
  · exact (isIntegral_algHom_iff (D.host.F.subtype.toIntAlgHom) Subtype.val_injective).mp
      (RingOfIntegers.isIntegral_coe z)
  · rfl

/- English proof (translation)
Set `cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E` to `RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv`. Establish `hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E)` using `fun y => rfl`. Establish `hinv` using `Formalism.L2.Host.conj_conj (D := D) D.host`. Establish `hpb : A.res v (cO A.piU) ≠ 0` using `A.res_conj v (cO A.piU) rfl`. Establish `hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0`.

Take `⟨zF, hzF⟩` from `exists_intF_of_conj_eq (D := D) (A.piU + cO A.piU) (by push_cast; simp only [hcO, map_add, hinv]; ring)`. Establish `hnot : zF ∉ (A.eV v).1.asIdeal`. Rewrite using `[A.res_v, hzF, map_add, A.res_pi, zero_add]`. Conclude with `hpb`. Rewrite `hnot` using `[hTau, hzF]`.

Use `le_antisymm (not_lt.mp fun h => hnot ?_) (Formalism.L2.Host.addVal_nonneg ν _)` and prove the remaining obligations. Use `push_cast`. Conclude with `lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)`. Establish `hpos : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E)`. Introduce `y hy`.

Establish `hy' : A.res v y = 0` using `hy`. Take `⟨zF, hzF⟩` from `exists_intF_of_conj_eq (D := D) (y * cO A.piU + cO y * A.piU) (by push_cast; simp only [hcO, map_add, map_mul, hinv]; ring)`. Establish `hin : zF ∈ (A.eV v).1.asIdeal`. Rewrite using `[A.res_v, hzF, map_add, map_mul, map_mul, hy', A.res_pi]`. Simplify using the standard rewrite rules.

Rewrite `hin` using `[hTau, hzF]`. Move the coercions through the operations in `at hin`. Establish `h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU)`. Rewrite using `[ν.map_mul]`. Conclude with `lt_of_lt_of_le hπ (le_add_of_nonneg_left (Formalism.L2.Host.addVal_nonneg ν _))`.

Establish `h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E))`. Establish `: (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) = ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) - ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU` using `by ring`. Rewrite using `[this]`. Conclude with `lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)`. Rewrite `h3` using `[ν.map_mul, hπb, add_zero]`. Then use the resulting hypothesis.

Establish `hPmax : (A.Pv v).IsMaximal` using `RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)`. Use `⟨fun h => ?_, hpos y⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hy`. Rewrite `h` using `[Formalism.L2.Host.addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hpos y hy]`. Conclude with `lt_irrefl _ h`.
-/
theorem pos_iff_mem_Pv (A : AtTTied u) (v : (D.mem u).A.vT) (ν : AddValuation D.host.E (WithTop ℤ))
    (hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E))
    (hπ : 0 < ν (A.piU : D.host.E)) (y : 𝓞 D.host.E) : 0 < ν (y : D.host.E) ↔ y ∈ A.Pv v := by
  let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have hcO : ∀ y : 𝓞 D.host.E, ((cO y : 𝓞 D.host.E) : D.host.E) = D.host.conj (y : D.host.E) := fun y => rfl
  have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
  have hpb : A.res v (cO A.piU) ≠ 0 := A.res_conj v (cO A.piU) rfl
  have hπb : ν ((cO A.piU : 𝓞 D.host.E) : D.host.E) = 0 := by
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (A.piU + cO A.piU) (by
      push_cast; simp only [hcO, map_add, hinv]; ring)
    have hnot : zF ∉ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add, A.res_pi, zero_add]; exact hpb
    rw [hTau, hzF] at hnot
    refine le_antisymm (not_lt.mp fun h => hnot ?_) (Formalism.L2.Host.addVal_nonneg ν _)
    push_cast
    exact lt_of_lt_of_le (lt_min hπ h) (ν.map_add _ _)
  have hpos : ∀ y ∈ A.Pv v, 0 < ν (y : D.host.E) := by
    intro y hy
    have hy' : A.res v y = 0 := hy
    obtain ⟨zF, hzF⟩ := exists_intF_of_conj_eq (D := D) (y * cO A.piU + cO y * A.piU) (by
      push_cast; simp only [hcO, map_add, map_mul, hinv]; ring)
    have hin : zF ∈ (A.eV v).1.asIdeal := by
      rw [A.res_v, hzF, map_add, map_mul, map_mul, hy', A.res_pi]; simp
    rw [hTau, hzF] at hin
    push_cast at hin
    have h2 : 0 < ν (((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) := by
      rw [ν.map_mul]; exact lt_of_lt_of_le hπ (le_add_of_nonneg_left (Formalism.L2.Host.addVal_nonneg ν _))
    have h3 : 0 < ν ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E)) := by
      have : (y : D.host.E) * (cO A.piU : 𝓞 D.host.E) =
          ((y : D.host.E) * (cO A.piU : 𝓞 D.host.E) + ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU) -
            ((cO y : 𝓞 D.host.E) : D.host.E) * A.piU := by ring
      rw [this]
      exact lt_of_lt_of_le (lt_min hin h2) (ν.map_sub _ _)
    rwa [ν.map_mul, hπb, add_zero] at h3
  have hPmax : (A.Pv v).IsMaximal := RingHom.ker_isMaximal_of_surjective (A.res v) (A.res_surj v)
  refine ⟨fun h => ?_, hpos y⟩
  by_contra hy
  rw [Formalism.L2.Host.addVal_eq_zero_of_not_mem ν (A.Pv v) hPmax hpos y hy] at h
  exact lt_irrefl _ h

/- English proof (translation)
Establish `e : (y : D.host.E) = star (x : D.host.E)` using `hxy.trans (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm`. Rewrite using `[Formalism.L2.Col.mem_conjIdeal]`. Establish `: Formalism.L2.Col.cO D.host.E x = y` using `RingOfIntegers.ext (by rw [e]; exact Formalism.L2.Col.algebraMap_cO x)`. Rewrite using `[this]`.
-/
theorem mem_conjIdeal_Pv (P : Ideal (𝓞 D.host.E)) (x y : 𝓞 D.host.E) (hxy : (y : D.host.E) = D.host.conj (x : D.host.E)) :
    x ∈ Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P ↔ y ∈ P := by
  have e : (y : D.host.E) = star (x : D.host.E) := hxy.trans (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [Formalism.L2.Col.mem_conjIdeal]
  have : Formalism.L2.Col.cO D.host.E x = y := RingOfIntegers.ext (by rw [e]; exact Formalism.L2.Col.algebraMap_cO x)
  rw [this]

/- English proof (translation)
Introduce `w hw v x y hy`. Set `σ : D.host.E ≃ₐ[ℚ] D.host.E` to `D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)`. Set `ν : AddValuation D.host.E (WithTop ℤ)` to `(D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))`. Establish `hyx : y = D.embE (σ (x : D.host.E))` using `D.what₂.embLL.injective (hy.trans (RingHom.congr_fun D.embE_φ₀ (σ (x : D.host.E))).symm)`. Establish `hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔ 0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)` using `fun zF => A.tauOf w hw v zF`.

Establish `hseen` using `A.seenP w hw ((D.fm u).tauOf w v)`. Substitute `hyx` using the available equality. Distinguish the cases in `hs : (D.fm u).seenP w = true`. Rewrite `hseen`, the goal using `[if_pos hs]`. Conclude with `pos_iff_mem_Pv A v ν hTau hseen x`.

Rewrite `hseen`, the goal using `[if_neg hs]`. Set `cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E` to `RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv`. Set `ν' : AddValuation D.host.E (WithTop ℤ)` to `ν.comap (D.host.conj : D.host.E →+* D.host.E)`. Establish `hinv` using `Formalism.L2.Host.conj_conj (D := D) D.host`. Establish `hfix : ∀ zF : 𝓞 D.host.F, D.host.conj (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)) = ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)` using `fun zF => (D.host.conjE_mem_hostF_iff _).1 (zF : D.host.F).2`.

Establish `hTau' : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔ 0 < ν' ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)` using `fun zF => by`. Rewrite using `[hTau]`. Use `show _ ↔ 0 < ν (D.host.conj _)`. Rewrite using `[hfix]`. Establish `h1` using `pos_iff_mem_Pv A v ν' hTau' hseen (cO x)`.

Rewrite using `[mem_conjIdeal_Pv (A.Pv v) x (cO x) rfl, ← h1]`. Use `show _ ↔ 0 < ν (D.host.conj (D.host.conj (x : D.host.E)))`. Rewrite using `[hinv]`. Both sides reduce to the same expression.
-/
theorem seenCl_of (A : AtTTied u) : SeenCl A := by
  intro w hw v x y hy
  let σ : D.host.E ≃ₐ[ℚ] D.host.E := D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
  let ν : AddValuation D.host.E (WithTop ℤ) :=
    (D.what₂.places.val w).comap (D.embE.comp (σ : D.host.E →+* D.host.E))
  have hyx : y = D.embE (σ (x : D.host.E)) :=
    D.what₂.embLL.injective (hy.trans (RingHom.congr_fun D.embE_φ₀ (σ (x : D.host.E))).symm)
  have hTau : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
      0 < ν ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
    A.tauOf w hw v zF
  have hseen := A.seenP w hw ((D.fm u).tauOf w v)
  subst hyx
  by_cases hs : (D.fm u).seenP w = true
  · rw [if_pos hs] at hseen ⊢
    exact pos_iff_mem_Pv A v ν hTau hseen x
  · rw [if_neg hs] at hseen ⊢
    let cO : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
    let ν' : AddValuation D.host.E (WithTop ℤ) := ν.comap (D.host.conj : D.host.E →+* D.host.E)
    have hinv := Formalism.L2.Host.conj_conj (D := D) D.host
    have hfix : ∀ zF : 𝓞 D.host.F, D.host.conj (((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E)) =
        ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF =>
      (D.host.conjE_mem_hostF_iff _).1 (zF : D.host.F).2
    have hTau' : ∀ zF : 𝓞 D.host.F, zF ∈ (A.eV v).1.asIdeal ↔
        0 < ν' ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) zF : 𝓞 D.host.E) : D.host.E) := fun zF => by
      rw [hTau]
      show _ ↔ 0 < ν (D.host.conj _)
      rw [hfix]
    have h1 := pos_iff_mem_Pv A v ν' hTau' hseen (cO x)
    rw [mem_conjIdeal_Pv (A.Pv v) x (cO x) rfl, ← h1]
    show _ ↔ 0 < ν (D.host.conj (D.host.conj (x : D.host.E)))
    rw [hinv]
    rfl

/- English proof (translation)
Introduce `_ _ _ _ _ _ F _ _ u` and use `seenCl_of (F u).atT`.
-/
theorem seenCl_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, SeenCl (F u).atT :=
  fun _ _ _ _ _ _ F _ _ u => seenCl_of (F u).atT

end GlobalTheory.Mem.Col2.HAt

end
