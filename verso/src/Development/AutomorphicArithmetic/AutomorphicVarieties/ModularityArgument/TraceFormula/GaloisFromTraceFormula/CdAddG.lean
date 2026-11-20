import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.WeilBound.RepresentationTheoryGL.JacquetShalikaBounds.AbsoluteRigidity.SatakeTwists.SatakeTwistHolds

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

/- English proof (translation)
Introduce `E _ _ _ r s D₁ D₂ ν ν' hr hs`. Set `e : Fin (D₁.c + D₂.c) ≃ Fin D₁.c ⊕ Fin D₂.c` to `finSumFinEquiv.symm`. Set `Q : Fin D₁.c ⊕ Fin D₂.c → Σ k, CG E k` to `Sum.elim (fun i => ⟨_, (D₁.P i).twist ν⟩) fun i => ⟨_, (D₂.P i).twist ν'⟩`. Use `⟨⟨D₁.c + D₂.c, fun i => (Q (e i)).1, fun i => (Q (e i)).2, fun i => ?_, ?_⟩, fun π hπ => ?_, fun w B₁ B₂ h h' ⟨b₁, c₁, d₁⟩ ⟨b₂, c₂, d₂⟩ => ⟨fun i => Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i), fun i : Fin (D₁.c + D₂.c) => ?_, ?_⟩, fun …` and prove the remaining obligations. Break down `e i with i | i exacts [D₁.pos i, D₂.pos i]` into its components or cases.

Rewrite using `[e.sum_comp fun o => (Q o).1, Fintype.sum_sum_type]`. Conclude with `congrArg₂ (· + ·) D₁.sum D₂.sum`. Take `⟨i, hi⟩` from `hπ`. Establish `h1 : (Q (e i)).1 = r + s` using `congrArg Sigma.fst hi`. Use `revert h1`.

Break down `e i with i | i` into its components or cases. Introduce `h1`. Establish `h2 : D₁.N i ≤ r` using `(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₁.sum.le`. Establish `h3 : D₁.N i = r + s` using `h1`. Use linear arithmetic over natural numbers and integers.

Introduce `h1`. Establish `h2 : D₂.N i ≤ s` using `(Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₂.sum.le`. Establish `h3 : D₂.N i = r + s` using `h1`. Use linear arithmetic over natural numbers and integers. Use `show (Q (e i)).2.HasSat w (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i))`.

Break down `e i with i | i` into its components or cases. Use `exacts [PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h (c₁ i), PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h' (c₂ i)]`. Use `show ∑ i : Fin (D₁.c + D₂.c), _ = _`. Rewrite using `[e.sum_comp (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) fun i => (b₂ i).map (· * ν'.val w)), Fintype.sum_sum_type, ← d₁, ← d₂]`. Conclude with `congrArg₂ (· + ·) (map_sum (Multiset.mapAddMonoidHom _) _ _).symm (map_sum (Multiset.mapAddMonoidHom _) _ _).symm`.

Use `show ∑ i : Fin (D₁.c + D₂.c), (Q (e i)).2.infChar τ = _`. Rewrite using `[e.sum_comp fun o => (Q o).2.infChar τ, Fintype.sum_sum_type]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.cdAddG :
    CDAddG := by
  intro E _ _ _ r s D₁ D₂ ν ν' hr hs
  let e : Fin (D₁.c + D₂.c) ≃ Fin D₁.c ⊕ Fin D₂.c := finSumFinEquiv.symm
  let Q : Fin D₁.c ⊕ Fin D₂.c → Σ k, CG E k := Sum.elim (fun i => ⟨_, (D₁.P i).twist ν⟩) fun i => ⟨_, (D₂.P i).twist ν'⟩
  refine ⟨⟨D₁.c + D₂.c, fun i => (Q (e i)).1, fun i => (Q (e i)).2, fun i => ?_, ?_⟩, fun π hπ => ?_,
    fun w B₁ B₂ h h' ⟨b₁, c₁, d₁⟩ ⟨b₂, c₂, d₂⟩ => ⟨fun i => Sum.elim (fun i => (b₁ i).map (· * ν.val w))
      (fun i => (b₂ i).map (· * ν'.val w)) (e i), fun i : Fin (D₁.c + D₂.c) => ?_, ?_⟩, fun τ => ?_⟩
  · rcases e i with i | i
    exacts [D₁.pos i, D₂.pos i]
  · rw [e.sum_comp fun o => (Q o).1, Fintype.sum_sum_type]
    exact congrArg₂ (· + ·) D₁.sum D₂.sum
  · obtain ⟨i, hi⟩ := hπ
    have h1 : (Q (e i)).1 = r + s := congrArg Sigma.fst hi
    revert h1
    rcases e i with i | i
    · intro h1
      have h2 : D₁.N i ≤ r := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₁.sum.le
      have h3 : D₁.N i = r + s := h1
      omega
    · intro h1
      have h2 : D₂.N i ≤ s := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans D₂.sum.le
      have h3 : D₂.N i = r + s := h1
      omega
  · show (Q (e i)).2.HasSat w (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) (fun i => (b₂ i).map (· * ν'.val w)) (e i))
    rcases e i with i | i
    exacts [PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h (c₁ i), PositivityTheory.RgJS.satake_twist_holds E _ _ _ w _ h' (c₂ i)]
  · show ∑ i : Fin (D₁.c + D₂.c), _ = _
    rw [e.sum_comp (Sum.elim (fun i => (b₁ i).map (· * ν.val w)) fun i => (b₂ i).map (· * ν'.val w)), Fintype.sum_sum_type,
      ← d₁, ← d₂]
    exact congrArg₂ (· + ·) (map_sum (Multiset.mapAddMonoidHom _) _ _).symm (map_sum (Multiset.mapAddMonoidHom _) _ _).symm
  · show ∑ i : Fin (D₁.c + D₂.c), (Q (e i)).2.infChar τ = _
    rw [e.sum_comp fun o => (Q o).2.infChar τ, Fintype.sum_sum_type]
    rfl
