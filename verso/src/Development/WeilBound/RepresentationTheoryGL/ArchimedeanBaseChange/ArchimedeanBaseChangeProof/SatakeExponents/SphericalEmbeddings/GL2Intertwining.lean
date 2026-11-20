import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SphericalEmbeddings.PseSat

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.Rg.BcB.N3.GL2Intertwining

open PositivityTheory.Rg.BcB.N3 PositivityTheory.Rg.BcB.N3.Pse

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

/- English proof (translation)
Take `⟨p, hp, x, hx, rfl⟩` from `(GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.2.2.2.2.2.2.2 g`. Use `⟨((twist ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom) (deltaHalf k (fun _ : Fin n => Unit))).comp (leviProj k (points (Fin n))) ⟨p, hp⟩) 1, fun v hv => ?_⟩` and prove the remaining obligations. Establish `h1 : v.1.1 (p * x) = v.1.1 p`. Establish `h` using `congrArg (fun u : IndSp (points (Fin n)) ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom) => u.1.1 p) (hv ⟨x, hx⟩)`. Rewrite `h` using `[MonoidHom.one_apply, Units.val_one, one_smul]`.

Conclude with `h`. Establish `h2` using `v.1.2 ⟨p, hp⟩ 1`. Rewrite `h2` using `[mul_one]`. Rewrite using `[h1, h2]`. Use `conv_lhs => rw [show v.1.1 1 = v.1.1 1 • (1 : ℂ) by simp]`.

Rewrite using `[map_smul, smul_eq_mul, mul_comm]`.
-/
private theorem exists_scalar_fixed_indSp_unrChar (α : Fin n → ℂˣ) (g : GL (Fin n) k) :
    ∃ c : ℂ, ∀ v : IndSp (points (Fin n))
      ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom),
      v ∈ fixed (iP (k := k) α) (KO k (Fin n)) → v.1.1 g = c * v.1.1 1 := by
  obtain ⟨p, hp, x, hx, rfl⟩ :=
    (GlobalTheory.SmGL.LeviInt.levi_integral_facts k (Fin n) (Fin n) (fun _ => Unit) (points (Fin n))).2.2.2.2.2.2.2.2 g
  refine ⟨((twist ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)
      (deltaHalf k (fun _ : Fin n => Unit))).comp (leviProj k (points (Fin n))) ⟨p, hp⟩) 1, fun v hv => ?_⟩
  have h1 : v.1.1 (p * x) = v.1.1 p := by
    have h := congrArg (fun u : IndSp (points (Fin n))
      ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom) => u.1.1 p)
      (hv ⟨x, hx⟩)
    rw [MonoidHom.one_apply, Units.val_one, one_smul] at h
    exact h
  have h2 := v.1.2 ⟨p, hp⟩ 1
  rw [mul_one] at h2
  rw [h1, h2]
  conv_lhs => rw [show v.1.1 1 = v.1.1 1 • (1 : ℂ) by simp]
  rw [map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Take `⟨c, hc⟩` from `exists_scalar_fixed_indSp_unrChar α g`. Use `show w.1.1 1 • v.1.1 g = v.1.1 1 • w.1.1 g`.

Rewrite using `[hc v hv, hc w hw, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kline (α : Fin n → ℂˣ) {v w : IndSp (points (Fin n))
    ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)}
    (hv : v ∈ fixed (iP (k := k) α) (KO k (Fin n))) (hw : w ∈ fixed (iP (k := k) α) (KO k (Fin n))) :
    w.1.1 1 • v = v.1.1 1 • w := by
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨c, hc⟩ := exists_scalar_fixed_indSp_unrChar α g
  show w.1.1 1 • v.1.1 g = v.1.1 1 • w.1.1 g
  rw [hc v hv, hc w hw, smul_eq_mul, smul_eq_mul]
  ring

/- English proof (translation)
Introduce `h1`. Apply `h0` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`.

Take `⟨c, hc⟩` from `exists_scalar_fixed_indSp_unrChar α g`. Rewrite using `[hc w hw, h1, mul_zero]`. Both sides reduce to the same expression.
-/
theorem one_ne_zero_of_fixed (α : Fin n → ℂˣ) {w : IndSp (points (Fin n))
    ((ofChar (torusChar fun i => unrChar k (α i))).comp (leviTorus k (Fin n)).symm.toMonoidHom)}
    (hw : w ∈ fixed (iP (k := k) α) (KO k (Fin n))) (h0 : w ≠ 0) : w.1.1 1 ≠ 0 := by
  intro h1
  apply h0
  apply Subtype.ext
  apply Subtype.ext
  funext g
  obtain ⟨c, hc⟩ := exists_scalar_fixed_indSp_unrChar α g
  rw [hc w hw, h1, mul_zero]
  rfl

end PositivityTheory.Rg.BcB.N3.GL2Intertwining
