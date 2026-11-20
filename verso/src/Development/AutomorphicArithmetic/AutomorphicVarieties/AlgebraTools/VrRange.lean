import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqLagIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic

open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

section aux

variable {B E : Type} [CommRing B] [Ring E] [Algebra B E] {T : TrInv B E} {ι : Type} [Fintype ι] [DecidableEq ι]
  {o : ι → ι} (U : T.Units ι o) (p q : ι)

private noncomputable def vrEnt (w : E) : (U.oddForm p q).Ext :=
  (U.oddForm p q).el (T.tr w)
    (cornerProj B (U.ep p) (U.ep q) w + cornerProj B (U.ep p) (U.ep q) (T.st w))

private noncomputable def vrRec (a b : ι) (z : (U.oddForm p q).Ext) : E :=
  if a = b then z.ev • U.ep a else if a = p then z.od.1 else T.st z.od.1

omit [DecidableEq ι] in
/- English proof (translation)
Simplify using `only [mul_assoc]`. Both sides reduce to the same expression.
-/
private theorem vrEnt_od (w : E) :
    (vrEnt U p q w).od.1 = U.ep p * w * U.ep q + U.ep p * T.st w * U.ep q := by
  simp only [mul_assoc]; rfl

omit [DecidableEq ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem vrEnt_ev (w : E) : (vrEnt U p q w).ev = T.tr w := rfl

omit [DecidableEq ι] in
/- English proof (translation)
Rewrite using `[← hw]`. Simplify using `only [mul_assoc]`. Break down `h with h | h` into its components or cases. Rewrite using `[← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]`. Rewrite using `[U.coi.ortho h, mul_zero, mul_zero, mul_zero]`.
-/
private theorem sand (a b c d : ι) (w : E) (hw : U.ep a * w * U.ep b = w) (h : c ≠ a ∨ b ≠ d) :
    U.ep c * w * U.ep d = 0 := by
  rw [← hw]
  simp only [mul_assoc]
  rcases h with h | h
  · rw [← mul_assoc (U.ep c), U.coi.ortho h, zero_mul]
  · rw [U.coi.ortho h, mul_zero, mul_zero, mul_zero]

omit [DecidableEq ι] in
/- English proof (translation)
Use `conv_rhs => rw [← hw]`. Rewrite using `[T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]`.
-/
private theorem sand_st (a b : ι) (w : E) (hw : U.ep a * w * U.ep b = w) :
    U.ep b * T.st w * U.ep a = T.st w := by
  conv_rhs => rw [← hw]
  rw [T.st_mul, T.st_mul, U.st_ep, U.st_ep, mul_assoc]

/- English proof (translation)
Establish `hst` using `sand_st U a b w hw`. Use `⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite `hw`, `hst` using `[← hab]`. Establish `h1 : p ≠ a ∨ a ≠ q`. Break down `ha with h | h` into its components or cases.

Conclude with `Or.inr (fun h' => hpq (h.symm.trans h'))`. Conclude with `Or.inl (fun h' => hpq (h'.trans h))`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]`. Both sides reduce to the same expression.

Rewrite using `[vrEnt_ev, ← hw]`. Conclude with `(units_basic T o U).2.2.1 a b w hab`. Unfold `vrRec split_ifs with h1 h2`. Rewrite `hw` using `[← h1]`. Rewrite using `[vrEnt_ev]`.

Use `conv_rhs => rw [← hw, U.corner_eq, hw]`. Establish `hb' : b = q` using `hb.resolve_left (fun h => h1 (h2.trans h.symm))`. Rewrite `hw`, `hst` using `[h2, hb']`. Rewrite using `[vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]`. Establish `ha' : a = q` using `ha.resolve_left h2`.

Establish `hb' : b = p` using `hb.resolve_right (fun h => h1 (ha'.trans h.symm))`. Rewrite `hw`, `hst` using `[ha', hb']`. Rewrite using `[vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]`.
-/
private theorem ent_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q) (w : E)
    (hw : U.ep a * w * U.ep b = w) :
    ((a = b → (vrEnt U p q w).od = 0) ∧ (a ≠ b → (vrEnt U p q w).ev = 0)) ∧
      vrRec U p q a b (vrEnt U p q w) = w := by
  have hst := sand_st U a b w hw
  refine ⟨⟨fun hab => ?_, fun hab => ?_⟩, ?_⟩
  · rw [← hab] at hw hst
    have h1 : p ≠ a ∨ a ≠ q := by
      rcases ha with h | h
      · exact Or.inr (fun h' => hpq (h.symm.trans h'))
      · exact Or.inl (fun h' => hpq (h'.trans h))
    apply Subtype.ext
    rw [vrEnt_od, sand U a a p q w hw h1, sand U a a p q (T.st w) hst h1, add_zero]
    rfl
  · rw [vrEnt_ev, ← hw]
    exact (units_basic T o U).2.2.1 a b w hab
  · unfold vrRec
    split_ifs with h1 h2
    · rw [← h1] at hw
      rw [vrEnt_ev]
      conv_rhs => rw [← hw, U.corner_eq, hw]
    · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
      rw [h2, hb'] at hw hst
      rw [vrEnt_od, hw, sand U q p p q (T.st w) hst (Or.inl hpq), add_zero]
    · have ha' : a = q := ha.resolve_left h2
      have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
      rw [ha', hb'] at hw hst
      rw [vrEnt_od, sand U q p p q w hw (Or.inl hpq), zero_add, hst, T.st_st]

/- English proof (translation)
Establish `hid : ∀ i, U.ep i * U.ep i = U.ep i` using `fun i => (U.coi.idem i).eq`. Establish `hmem : U.ep p * (z.od : E) * U.ep q = z.od`. Take `⟨y, hy⟩` from `z.od.2`. Rewrite using `[← hy]`. Use `show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)`.

Rewrite using `[← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]`. Establish `hoff : U.ep p * T.st (z.od : E) * U.ep q = 0` using `sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)`. Unfold `vrRec`. Use `split_ifs with h1 h2`. Establish `hod` using `hz.1 h1`.

Establish `hpa : U.ep p * U.ep a * U.ep q = 0`. Break down `ha with h | h` into its components or cases. Rewrite using `[h, hid, U.coi.ortho hpq]`. Rewrite using `[h, U.coi.ortho hpq, zero_mul]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← h1, mul_smul_comm, smul_mul_assoc, hid, hid]`. Apply `OddForm.Ext.ext` to reduce the goal to its premises. Rewrite using `[vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[vrEnt_od, hod, map_smul, U.st_ep]`.

Simplify using `only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]`. Both sides reduce to the same expression. Establish `hb' : b = q` using `hb.resolve_left (fun h => h1 (h2.trans h.symm))`. Establish `hev` using `hz.2 h1`. Rewrite using `[h2, hb']`.

Use `⟨hmem, ?_⟩` and prove the remaining obligations. Apply `OddForm.Ext.ext` to reduce the goal to its premises. Rewrite using `[vrEnt_ev, hev, ← hmem]`. Conclude with `(units_basic T o U).2.2.1 p q _ hpq`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[vrEnt_od, hmem, hoff, add_zero]`. Establish `ha' : a = q` using `ha.resolve_left h2`. Establish `hb' : b = p` using `hb.resolve_right (fun h => h1 (ha'.trans h.symm))`. Establish `hev` using `hz.2 h1`. Rewrite using `[ha', hb']`.

Use `⟨sand_st U p q _ hmem, ?_⟩` and prove the remaining obligations. Apply `OddForm.Ext.ext` to reduce the goal to its premises. Rewrite using `[vrEnt_ev, T.tr_st, hev, ← hmem]`. Conclude with `(units_basic T o U).2.2.1 p q _ hpq`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[vrEnt_od, T.st_st, hmem, hoff, zero_add]`.
-/
private theorem rec_spec (hpq : p ≠ q) (a b : ι) (ha : a = p ∨ a = q) (hb : b = p ∨ b = q)
    (z : (U.oddForm p q).Ext) (hz : (a = b → z.od = 0) ∧ (a ≠ b → z.ev = 0)) :
    U.ep a * vrRec U p q a b z * U.ep b = vrRec U p q a b z ∧ vrEnt U p q (vrRec U p q a b z) = z := by
  have hid : ∀ i, U.ep i * U.ep i = U.ep i := fun i => (U.coi.idem i).eq
  have hmem : U.ep p * (z.od : E) * U.ep q = z.od := by
    obtain ⟨y, hy⟩ := z.od.2
    rw [← hy]
    show U.ep p * (U.ep p * (y * U.ep q)) * U.ep q = U.ep p * (y * U.ep q)
    rw [← mul_assoc (U.ep p) (U.ep p), hid, mul_assoc, mul_assoc, hid]
  have hoff : U.ep p * T.st (z.od : E) * U.ep q = 0 :=
    sand U q p p q _ (sand_st U p q _ hmem) (Or.inl hpq)
  unfold vrRec
  split_ifs with h1 h2
  · have hod := hz.1 h1
    have hpa : U.ep p * U.ep a * U.ep q = 0 := by
      rcases ha with h | h
      · rw [h, hid, U.coi.ortho hpq]
      · rw [h, U.coi.ortho hpq, zero_mul]
    refine ⟨?_, ?_⟩
    · rw [← h1, mul_smul_comm, smul_mul_assoc, hid, hid]
    · apply OddForm.Ext.ext
      · rw [vrEnt_ev, map_smul, U.tr_ep, smul_eq_mul, mul_one]
      · apply Subtype.ext
        rw [vrEnt_od, hod, map_smul, U.st_ep]
        simp only [mul_smul_comm, smul_mul_assoc, hpa, smul_zero, add_zero]
        rfl
  · have hb' : b = q := hb.resolve_left (fun h => h1 (h2.trans h.symm))
    have hev := hz.2 h1
    rw [h2, hb']
    refine ⟨hmem, ?_⟩
    apply OddForm.Ext.ext
    · rw [vrEnt_ev, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · apply Subtype.ext
      rw [vrEnt_od, hmem, hoff, add_zero]
  · have ha' : a = q := ha.resolve_left h2
    have hb' : b = p := hb.resolve_right (fun h => h1 (ha'.trans h.symm))
    have hev := hz.2 h1
    rw [ha', hb']
    refine ⟨sand_st U p q _ hmem, ?_⟩
    apply OddForm.Ext.ext
    · rw [vrEnt_ev, T.tr_st, hev, ← hmem]
      exact (units_basic T o U).2.2.1 p q _ hpq
    · apply Subtype.ext
      rw [vrEnt_od, T.st_st, hmem, hoff, zero_add]

end aux

/- English proof (translation)
Introduce `B E _ _ _ T ι _ _ o U p q hpq ho`. Take `⟨hxx, -, -, -, -, hsum, hcor⟩` from `units_basic T o U`. Establish `hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j))` using `fun _ _ _ => rfl`. Establish `hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j)`. Introduce `w i j`.

Rewrite using `[hvr]`. Conclude with `(ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2`. Establish `hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0`. Introduce `i k`. Use `split_ifs with h`.

Rewrite using `[h, U.x_st]`. Conclude with `hxx i k h`. Use `⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hsum w, hsum w']`. Use `Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))` and prove the remaining obligations.

Rewrite using `[← hrec w i j, ← hrec w' i j, h]`. Introduce and unpack `⟨w, rfl⟩ i j`. Rewrite using `[hvr]`. Conclude with `(ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1`. Introduce `hY`.

Use `⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩` and prove the remaining obligations. Use `Matrix.ext (fun i j => ?_)` and prove the remaining obligations. Rewrite using `[hvr]`. Establish `hr` using `rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)`. Establish `key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) * T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum, Finset.sum_mul, mul_assoc]`. Use `_ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by`. Simplify using `[hx]`. Use `_ = vrRec U p q (o i) (o j) (Y i j) := hr.1`.

Rewrite using `[key]`. Conclude with `hr.2`.
-/
theorem UpperTheory.V.AlgebraTools.vr_range :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (p q : ι), p ≠ q → (∀ i, o i = p ∨ o i = q) → Function.Injective (U.vr p q) ∧ ∀ Y : Matrix ι ι (U.oddForm p q).Ext, Y ∈ Set.range (U.vr p q) ↔ ∀ i j, (o i = o j → (Y i j).od = 0) ∧ (o i ≠ o j → (Y i j).ev = 0) := by
  intro B E _ _ _ T ι _ _ o U p q hpq ho
  obtain ⟨hxx, -, -, -, -, hsum, hcor⟩ := units_basic T o U
  have hvr : ∀ w i j, U.vr p q w i j = vrEnt U p q (U.x i * w * T.st (U.x j)) :=
    fun _ _ _ => rfl
  have hrec : ∀ w i j, vrRec U p q (o i) (o j) (U.vr p q w i j) = U.x i * w * T.st (U.x j) := by
    intro w i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).2
  have hx : ∀ i k, U.x i * T.st (U.x k) = if i = k then U.ep (o i) else 0 := by
    intro i k
    split_ifs with h
    · rw [h, U.x_st]
    · exact hxx i k h
  refine ⟨fun w w' h => ?_, fun Y => ⟨?_, ?_⟩⟩
  · rw [hsum w, hsum w']
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [← hrec w i j, ← hrec w' i j, h]
  · rintro ⟨w, rfl⟩ i j
    rw [hvr]
    exact (ent_spec U p q hpq (o i) (o j) (ho i) (ho j) _ (hcor i j w)).1
  · intro hY
    refine ⟨∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l, ?_⟩
    refine Matrix.ext (fun i j => ?_)
    rw [hvr]
    have hr := rec_spec U p q hpq (o i) (o j) (ho i) (ho j) (Y i j) (hY i j)
    have key : U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
        T.st (U.x j) = vrRec U p q (o i) (o j) (Y i j) := by
      calc U.x i * (∑ k, ∑ l, T.st (U.x k) * vrRec U p q (o k) (o l) (Y k l) * U.x l) *
            T.st (U.x j)
          = ∑ k, ∑ l, (U.x i * T.st (U.x k)) * vrRec U p q (o k) (o l) (Y k l) *
              (U.x l * T.st (U.x j)) := by
            simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        _ = U.ep (o i) * vrRec U p q (o i) (o j) (Y i j) * U.ep (o j) := by
            simp [hx]
        _ = vrRec U p q (o i) (o j) (Y i j) := hr.1
    rw [key]
    exact hr.2
