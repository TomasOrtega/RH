import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ThetaDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.VrReduction
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

section aux

variable {B N : Type} [CommRing B] [AddCommGroup N] [Module B N] (Φ : OddForm B N)

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, OddForm.ev_smul, OddForm.ev_one, mul_one]`.
-/
private theorem ev_alg (b : B) : (algebraMap B Φ.Ext b).ev = b := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.ev_smul, OddForm.ev_one, mul_one]

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one, OddForm.od_smul, OddForm.od_one, smul_zero]`.
-/
private theorem od_alg (b : B) : (algebraMap B Φ.Ext b).od = 0 := by
  rw [Algebra.algebraMap_eq_smul_one, OddForm.od_smul, OddForm.od_one, smul_zero]

/- English proof (translation)
Rewrite using `[Submodule.mem_one]`. Use `⟨?_, fun h => ⟨z.ev, OddForm.Ext.ext (ev_alg Φ _) (by rw [od_alg, h])⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨b, rfl⟩`. Conclude with `od_alg Φ b`.
-/
private theorem mem_one_iff (z : Φ.Ext) : z ∈ (1 : Submodule B Φ.Ext) ↔ z.od = 0 := by
  rw [Submodule.mem_one]
  refine ⟨?_, fun h => ⟨z.ev, OddForm.Ext.ext (ev_alg Φ _) (by rw [od_alg, h])⟩⟩
  rintro ⟨b, rfl⟩
  exact od_alg Φ b

private def oddPart : Submodule B Φ.Ext where
  carrier := {z | z.ev = 0}
  add_mem' := fun {x y} (hx : x.ev = 0) (hy : y.ev = 0) => show (x + y).ev = 0 by
    rw [OddForm.ev_add, hx, hy, add_zero]
  zero_mem' := rfl
  smul_mem' := fun c x (hx : x.ev = 0) => show (c • x).ev = 0 by
    rw [OddForm.ev_smul, hx, mul_zero]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private theorem mem_oddPart (z : Φ.Ext) : z ∈ oddPart Φ ↔ z.ev = 0 := Iff.rfl

/- English proof (translation)
Use `⟨Submodule.disjoint_def.2 fun z h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun z _ => ?_)⟩` and prove the remaining obligations. Conclude with `OddForm.Ext.ext ((mem_oddPart Φ z).1 h2) ((mem_one_iff Φ z).1 h1)`. Use `Submodule.mem_sup.2 ⟨Φ.el z.ev 0, (mem_one_iff Φ _).2 rfl, Φ.el 0 z.od, rfl, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `ext <;> simp`.
-/
private theorem compl_oddPart : _root_.IsCompl (1 : Submodule B Φ.Ext) (oddPart Φ) := by
  refine ⟨Submodule.disjoint_def.2 fun z h1 h2 => ?_, codisjoint_iff.2 (eq_top_iff.2 fun z _ => ?_)⟩
  · exact OddForm.Ext.ext ((mem_oddPart Φ z).1 h2) ((mem_one_iff Φ z).1 h1)
  · refine Submodule.mem_sup.2 ⟨Φ.el z.ev 0, (mem_one_iff Φ _).2 rfl, Φ.el 0 z.od, rfl, ?_⟩
    ext <;> simp

end aux

/- English proof (translation)
Unfold `oB`. Apply the tactic sequence `by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega`.
-/
private theorem oB_eq_iff {n a : ℕ} (h1 : 1 ≤ a) (h2 : a < n) (i j : Fin n) :
    oB n a i = oB n a j ↔ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) := by
  unfold oB
  by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] <;> omega

/- English proof (translation)
Introduce `B E F _ _ _ _ _ _ n _ a T r U h1 h2 hker hst hx hev`. Set `p : Fin n` to `⟨0, by omega⟩`. Set `q : Fin n` to `⟨n - 1, by omega⟩`. Establish `hpq : p ≠ q` using `fun h => by`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `only [p, q] at this`. Use linear arithmetic over natural numbers and integers. Establish `ho : ∀ i, oB n a i = p ∨ oB n a i = q` using `fun i => by`. Unfold `oB`. Use `split_ifs`.

Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`. Establish `hp : oB n a p = p`. Unfold `oB`. Rewrite using `[if_pos (show 0 < a by omega)]`.

Establish `hq : oB n a q = q`. Unfold `oB`. Rewrite using `[if_neg (show ¬ (n - 1 < a) by omega)]`. Establish `h0 : ∀ y i j, oB n a i ≠ oB n a j → r y i j = 0` using `fun y i j h => (Submodule.mem_bot F).1 ((hev y i j).2 fun h' => h ((oB_eq_iff h1 h2 i j).2 h'))`. Take `⟨φ, hφ, hφst, -⟩` from `vr_hom T (oB n a) U p q hpq ho`.

Take `⟨hinj, hrange⟩` from `vr_range T (oB n a) U p q hpq ho`. Take `⟨hred, hle⟩` from `vr_reduction T (oB n a) U r p q hst hx h0`. Establish `hle'` using `hle hp hq hpq`. Rewrite `hle'` using `[hker]`. Establish `hφe : (φ : E → _) = U.vr p q` using `funext hφ`.

Use `haveI : Module.Finite B (corner B (U.ep p) (U.ep q)) := Module.Finite.range _`. Establish `hv : ∀ y y' k l, U.x k * y * T.st (U.x l) = U.x k * y' * T.st (U.x l) → φ y k l = φ y' k l` using `fun y y' k l h => by`. Rewrite using `[hφ, hφ]`. Simplify using `only [TrInv.Units.vr, Matrix.of_apply, h]`. Establish `ha : ∀ i, U.x i * U.ep i = U.x i` using `fun i => by conv_lhs => rw [← U.x_mem i, mul_assoc, (U.coi.idem i).eq]`.

Conclude with `U.x_mem i`. Establish `hd : ∀ i, U.ep i * T.st (U.x i) = T.st (U.x i)` using `fun i => by`. Rewrite using `[← U.st_ep i, ← T.st_mul, ha]`. Use `⟨{ AA := (U.oddForm p q).Ext fin := inferInstance inj := fun b b' h => ?_ N := oddPart _ compl := compl_oddPart _ mul_mem := fun y hy z hz => ?_ typeI := fun h => absurd h h2.ne φ := φ φ_inj := hφe ▸ hinj range := fun Y => ?_ st := hφst φ_ep := fun i => ?_ red := fun y i j b h => …` and prove the remaining obligations. Rewrite using `[← ev_alg (U.oddForm p q) b, h, ev_alg]`.

Rewrite `hy`, `hz` using `[mem_oddPart]`. Use `⟨(U.oddForm p q).be y.od z.od, hle' (Ideal.subset_span ⟨_, _, rfl⟩), OddForm.Ext.ext ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[ev_alg, OddForm.ev_mul, hy, zero_mul, zero_add]`. Rewrite using `[od_alg, OddForm.od_mul, hy, hz, zero_smul, zero_smul, add_zero]`. Rewrite using `[hφe, hrange]`.

Use `forall_congr' fun i => forall_congr' fun j => ?_` and prove the remaining obligations. Rewrite using `[mem_one_iff, mem_oddPart, Ne, oB_eq_iff h1 h2]`. Use `ext1 k l`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality.

Distinguish the cases in `hl : l = k`. Substitute `hl` using the available equality. Rewrite using `[hv (U.ep l) 1 l l (by rw [ha, mul_one]), map_one, one_apply_eq, single_apply_same]`. Establish `e : U.ep k * U.ep l = 0` using `U.coi.ortho (Ne.symm hl)`. Rewrite using `[hv (U.ep k) 0 k l (by rw [← hd l, mul_assoc, ← mul_assoc (U.ep k), e]; simp), map_zero, single_apply_of_col_ne _ _ (Ne.symm hl), Matrix.zero_apply]`.

Establish `e : U.ep k * U.ep i = 0` using `U.coi.ortho hk`. Rewrite using `[hv (U.ep i) 0 k l (by rw [← ha k, mul_assoc (U.x k), e]; simp), map_zero, single_apply_of_row_ne (Ne.symm hk), Matrix.zero_apply]`. Rewrite using `[← hred y i j, ← hφ]`. Establish `e : φ y i j = (φ y i j - algebraMap B _ b) + algebraMap B _ b` using `(sub_add_cancel _ _).symm`. Rewrite using `[e, OddForm.ev_add, (mem_oddPart _ _).1 h, ev_alg, zero_add]`.
-/
theorem UpperTheory.V.Pa.gr_E :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} [Module.Finite B E] (a : ℕ) (T : TrInv B E) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (U : T.Units (Fin n) (oB n a)), 1 ≤ a → a < n → RingHom.ker (algebraMap B F) = maximalIdeal B → (∀ y, r (T.st y) = (r y)ᵀ) → (∀ i, r (U.x i) = single (oB n a i) i 1) → (∀ y, r y ∈ Ev F F n a) → Nonempty (GrAlg T n a r U.ep) := by
  intro B E F _ _ _ _ _ _ n _ a T r U h1 h2 hker hst hx hev
  let p : Fin n := ⟨0, by omega⟩
  let q : Fin n := ⟨n - 1, by omega⟩
  have hpq : p ≠ q := fun h => by
    have := congrArg Fin.val h
    simp only [p, q] at this
    omega
  have ho : ∀ i, oB n a i = p ∨ oB n a i = q := fun i => by
    unfold oB
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hp : oB n a p = p := by
    unfold oB
    rw [if_pos (show 0 < a by omega)]
  have hq : oB n a q = q := by
    unfold oB
    rw [if_neg (show ¬ (n - 1 < a) by omega)]
  have h0 : ∀ y i j, oB n a i ≠ oB n a j → r y i j = 0 := fun y i j h =>
    (Submodule.mem_bot F).1 ((hev y i j).2 fun h' => h ((oB_eq_iff h1 h2 i j).2 h'))
  obtain ⟨φ, hφ, hφst, -⟩ := vr_hom T (oB n a) U p q hpq ho
  obtain ⟨hinj, hrange⟩ := vr_range T (oB n a) U p q hpq ho
  obtain ⟨hred, hle⟩ := vr_reduction T (oB n a) U r p q hst hx h0
  have hle' := hle hp hq hpq
  rw [hker] at hle'
  have hφe : (φ : E → _) = U.vr p q := funext hφ
  haveI : Module.Finite B (corner B (U.ep p) (U.ep q)) := Module.Finite.range _
  have hv : ∀ y y' k l, U.x k * y * T.st (U.x l) = U.x k * y' * T.st (U.x l) → φ y k l = φ y' k l :=
    fun y y' k l h => by
      rw [hφ, hφ]
      simp only [TrInv.Units.vr, Matrix.of_apply, h]
  have ha : ∀ i, U.x i * U.ep i = U.x i := fun i => by
    conv_lhs => rw [← U.x_mem i, mul_assoc, (U.coi.idem i).eq]
    exact U.x_mem i
  have hd : ∀ i, U.ep i * T.st (U.x i) = T.st (U.x i) := fun i => by
    rw [← U.st_ep i, ← T.st_mul, ha]
  refine ⟨{ AA := (U.oddForm p q).Ext
            fin := inferInstance
            inj := fun b b' h => ?_
            N := oddPart _
            compl := compl_oddPart _
            mul_mem := fun y hy z hz => ?_
            typeI := fun h => absurd h h2.ne
            φ := φ
            φ_inj := hφe ▸ hinj
            range := fun Y => ?_
            st := hφst
            φ_ep := fun i => ?_
            red := fun y i j b h => ?_ }⟩
  · rw [← ev_alg (U.oddForm p q) b, h, ev_alg]
  · rw [mem_oddPart] at hy hz
    refine ⟨(U.oddForm p q).be y.od z.od, hle' (Ideal.subset_span ⟨_, _, rfl⟩), OddForm.Ext.ext ?_ ?_⟩
    · rw [ev_alg, OddForm.ev_mul, hy, zero_mul, zero_add]
    · rw [od_alg, OddForm.od_mul, hy, hz, zero_smul, zero_smul, add_zero]
  · rw [hφe, hrange]
    refine forall_congr' fun i => forall_congr' fun j => ?_
    rw [mem_one_iff, mem_oddPart, Ne, oB_eq_iff h1 h2]
  · ext1 k l
    by_cases hk : k = i
    · subst hk
      by_cases hl : l = k
      · subst hl
        rw [hv (U.ep l) 1 l l (by rw [ha, mul_one]), map_one, one_apply_eq, single_apply_same]
      · have e : U.ep k * U.ep l = 0 := U.coi.ortho (Ne.symm hl)
        rw [hv (U.ep k) 0 k l (by rw [← hd l, mul_assoc, ← mul_assoc (U.ep k), e]; simp), map_zero,
          single_apply_of_col_ne _ _ (Ne.symm hl), Matrix.zero_apply]
    · have e : U.ep k * U.ep i = 0 := U.coi.ortho hk
      rw [hv (U.ep i) 0 k l (by rw [← ha k, mul_assoc (U.x k), e]; simp), map_zero,
        single_apply_of_row_ne (Ne.symm hk), Matrix.zero_apply]
  · rw [← hred y i j, ← hφ]
    have e : φ y i j = (φ y i j - algebraMap B _ b) + algebraMap B _ b := (sub_add_cancel _ _).symm
    rw [e, OddForm.ev_add, (mem_oddPart _ _).1 h, ev_alg, zero_add]
