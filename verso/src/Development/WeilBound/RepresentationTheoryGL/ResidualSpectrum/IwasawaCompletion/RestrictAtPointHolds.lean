import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.LsProps
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.ExistsIwasawaLeft

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3.Rap

open PositivityTheory.RSHS.LS PositivityTheory.Rg.Rs.C3.Fl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Assume the negation of the conclusion and derive a contradiction.

Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Both sides reduce to the same expression. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities.

Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs and assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem restrictAtPoint_holds : RestrictAtPoint := by
  intro E _ _ _ N c n h π w X _ _ ρ F hF
  obtain ⟨v0, hv0⟩ : ∃ v, F.1 v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hF (LinearMap.ext hc)
  obtain ⟨g0, hg0⟩ : ∃ g, (F.1 v0).1 g ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv0 (Subtype.ext (funext hc))
  obtain ⟨u, hu, m0, k, x, rfl⟩ := exists_iwasawa_left h g0
  let xw := Matrix.GeneralLinearGroup.map (pLoc E w) x
  let xo := x * (locGL E N w xw)⁻¹
  have hxo : Matrix.GeneralLinearGroup.map (pLoc E w) xo = 1 := by
    simp only [xo, map_mul, map_inv, pLoc_locGL]
    exact mul_inv_cancel _
  have hx : x = xo * locGL E N w xw := by simp [xo]
  let Lf : X → ((∀ i, GA E (n i)) → ℂ) := fun v m =>
    (F.1 v).1 (leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N xo))
  let L : X →ₗ[ℂ] ((∀ i, GA E (n i)) → ℂ) :=
    { toFun := Lf
      map_add' := fun v v' => by
        funext m
        simp only [Lf, map_add]
        rfl
      map_smul' := fun z v => by
        funext m
        simp only [Lf, map_smul]
        rfl }
  refine ⟨L, fun v => (F.2.1 v).2.2.2 k xo, ?_, ?_⟩
  · intro h0
    apply hg0
    have h1 := congrFun (LinearMap.congr_fun h0 (ρ xw v0)) m0
    change (F.1 (ρ xw v0)).1 _ = 0 at h1
    rw [F.2.2 xw v0] at h1
    change (F.1 v0).1 (_ * finGL E N (locGL E N w xw)) = 0 at h1
    have hfx : finGL E N x = finGL E N xo * finGL E N (locGL E N w xw) := by rw [← map_mul, ← hx]
    rw [(F.2.1 v0).1 u hu, hfx]
    simpa only [mul_assoc] using h1
  · intro p v
    funext m
    obtain ⟨up, hup, hp⟩ := exists_levi_mul_unip (w.adicCompletion E) (stdBlocks n h) p
    change (F.1 (ρ p v)).1 _ = (F.1 v).1 _
    rw [F.2.2 p v]
    change (F.1 v).1 (_ * finGL E N (locGL E N w (p : GL (Fin N) (w.adicCompletion E)))) = _
    let M' : ∀ i, GA E (n i) := fun i =>
      finGL E (n i) (locGL E (n i) w (leviProj (w.adicCompletion E) (stdBlocks n h) p i))
    have hq : finGL E N (locGL E N w p) =
        leviEmb (Ad E) (stdBlocks n h) M' * finGL E N (locGL E N w up) := by
      rw [hp, map_mul, map_mul]
      congr 1
      exact iota_leviEmb h _
    have hu' : finGL E N (locGL E N w up) ∈ unipRad (Ad E) (stdBlocks n h) := iota_mem_unipRad h hup
    have hcomm : infGL E N (Unitary.toUnits k) * finGL E N xo * finGL E N (locGL E N w p) =
        finGL E N (locGL E N w p) * (infGL E N (Unitary.toUnits k) * finGL E N xo) := by
      rw [mul_assoc, ← map_mul (finGL E N) xo, ← locGL_commute w xo _ hxo, map_mul, ← mul_assoc, infGL_comm, mul_assoc]
    have key : ∀ a b c' d : GA E N, a * (b * c' * d) = (a * b * c' * (a * b)⁻¹) * (a * b * d) := by
      intros
      group
    have hconj := (Subgroup.mem_normalizer_iff.1
      (leviEmb_mem_normalizer (Ad E) (stdBlocks n h) (m * M')) _).1 hu'
    rw [mul_assoc, hcomm, hq, key, ← map_mul, (F.2.1 v).1 _ hconj]
    rfl

end PositivityTheory.Rg.Rs.C3.Rap

end
