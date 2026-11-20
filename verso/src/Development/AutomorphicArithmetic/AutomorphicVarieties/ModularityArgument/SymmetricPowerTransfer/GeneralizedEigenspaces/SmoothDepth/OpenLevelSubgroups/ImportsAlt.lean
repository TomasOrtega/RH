import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.Factor
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanSph

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

/- English proof (translation)
Introduce `L _ _ _ n V _ _ _ R π hπ U hU S`. Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact fun _ _ W φ h0 hc h => ⟨φ, h0, hc, h.left, h.inf, fun u hu => h.level u (by simpa [lev] using hu)⟩`. Consider the case `insert w S hw ih`. Introduce `hS hK W φ h0 hc h`.

Establish `hwm : w ∈ insert w S` using `Finset.mem_insert_self _ _`. Take `⟨φ', a0, a1, a2⟩` from `spanSph L n V π hπ w (hK w hwm).2 φ h0 hc`. Take `⟨k1, k2, -⟩` from `spanKeep L n V w φ φ' a1`. Establish `hA : IsAF R (lev U S W ⊓ away n w) φ'` using `k2 R _ inf_le_right ⟨h.left, h.inf, fun u hu => h.level u (by`. Take `⟨h1, h2⟩` from `Subgroup.mem_inf.1 hu`.

Simplify using `only [lev, away, Subgroup.mem_inf, Subgroup.mem_iInf] at h1 h2 ⊢`. Use `⟨h1.1, fun w' hw' => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hw' with rfl | hw'` into its components or cases. Rewrite using `[Subgroup.mem_comap, MonoidHom.mem_ker.1 (h2 w' rfl)]`. Conclude with `one_mem _`.

Conclude with `h1.2 w' hw')⟩`. Use `ih ⟨fun u hu => hS.split u (Finset.mem_insert_of_mem hu), hS.inj.mono (by simp)⟩ (fun u hu => hK u (Finset.mem_insert_of_mem hu)) W φ' a0 (k1 π hπ hc) ⟨hA.left, hA.inf, fun u hu g => ?_⟩` and prove the remaining obligations. Take `⟨-, f2, -, -, -, f6⟩` from `factor L n w`. Take `⟨x, hx, y, hy, rfl⟩` from `f2 u`. Establish `hxK : x ∈ Kall L n` using `((f6 x hx y hy).1 (hU hu.1)).1`.

Establish `hxl : x ∈ lev U S W`. Simplify using `only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]`. Use `⟨(hK w hwm).1 ⟨hx, hxK⟩, fun w' hw' => ?_⟩` and prove the remaining obligations. Establish `hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L))` using `fun e => hw (hS.inj (Finset.mem_coe.2 hwm) (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw')) e ▸ hw')`. Use `(factor L n w').2.2.1 w hne hx` as an intermediate fact.

Simplify using `only [away, Subgroup.mem_iInf] at this`. Rewrite using `[Subgroup.mem_comap, MonoidHom.mem_ker.1 (this w' rfl)]`. Conclude with `one_mem _`. Establish `hyl : y ∈ lev U S W` using `(Subgroup.mul_mem_cancel_left _ hxl).1 hu`. Rewrite using `[← mul_assoc, hA.level y ⟨hyl, hy⟩, a2 x ⟨hx, hxK⟩]`.
-/
theorem UpperTheory.V.Z.Sym.Al.raise :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (π : Submodule ℂ (UA L n → ℂ)), IsAutRepU π →
        ∀ U : Subgroup (UA L n), U ≤ Kall L n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U ∧ IsUnramU π w) → ∀ (W : ∀ w : Plc L, Sig.Lev (Kw w)) (φ : UA L n → V), φ ≠ 0 → CoefIn φ π →
        IsAF R (lev U S W) φ → ∃ φ' : UA L n → V, φ' ≠ 0 ∧ CoefIn φ' π ∧ IsAF R U φ' := by
  classical
  intro L _ _ _ n V _ _ _ R π hπ U hU S
  induction S using Finset.induction_on with
  | empty => exact fun _ _ W φ h0 hc h => ⟨φ, h0, hc, h.left, h.inf, fun u hu => h.level u (by simpa [lev] using hu)⟩
  | insert w S hw ih =>
    intro hS hK W φ h0 hc h
    have hwm : w ∈ insert w S := Finset.mem_insert_self _ _
    obtain ⟨φ', a0, a1, a2⟩ := spanSph L n V π hπ w (hK w hwm).2 φ h0 hc
    obtain ⟨k1, k2, -⟩ := spanKeep L n V w φ φ' a1
    have hA : IsAF R (lev U S W ⊓ away n w) φ' := k2 R _ inf_le_right ⟨h.left, h.inf, fun u hu => h.level u (by
      obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hu
      simp only [lev, away, Subgroup.mem_inf, Subgroup.mem_iInf] at h1 h2 ⊢
      refine ⟨h1.1, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.1 hw' with rfl | hw'
      · rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (h2 w' rfl)]; exact one_mem _
      · exact h1.2 w' hw')⟩
    refine ih ⟨fun u hu => hS.split u (Finset.mem_insert_of_mem hu), hS.inj.mono (by simp)⟩
      (fun u hu => hK u (Finset.mem_insert_of_mem hu)) W φ' a0 (k1 π hπ hc) ⟨hA.left, hA.inf, fun u hu g => ?_⟩
    obtain ⟨-, f2, -, -, -, f6⟩ := factor L n w
    obtain ⟨x, hx, y, hy, rfl⟩ := f2 u
    have hxK : x ∈ Kall L n := ((f6 x hx y hy).1 (hU hu.1)).1
    have hxl : x ∈ lev U S W := by
      simp only [lev, Subgroup.mem_inf, Subgroup.mem_iInf]
      refine ⟨(hK w hwm).1 ⟨hx, hxK⟩, fun w' hw' => ?_⟩
      have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun e =>
        hw (hS.inj (Finset.mem_coe.2 hwm) (Finset.mem_coe.2 (Finset.mem_insert_of_mem hw')) e ▸ hw')
      have := (factor L n w').2.2.1 w hne hx
      simp only [away, Subgroup.mem_iInf] at this
      rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 (this w' rfl)]
      exact one_mem _
    have hyl : y ∈ lev U S W := (Subgroup.mul_mem_cancel_left _ hxl).1 hu
    rw [← mul_assoc, hA.level y ⟨hyl, hy⟩, a2 x ⟨hx, hxK⟩]
