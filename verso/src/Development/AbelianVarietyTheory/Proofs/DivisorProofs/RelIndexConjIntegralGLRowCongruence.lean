import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.DiagVol.RowIdx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Introduce `u v h`. Use extensionality with `i j`. Conclude with `congrArg (fun g : GL ι k => g.val i j) h`.
-/
theorem mapInt_injective :
    Function.Injective (Matrix.GeneralLinearGroup.map (n := ι) (algebraMap 𝒪[k] k)) := by
  intro u v h
  ext i j
  exact congrArg (fun g : GL ι k => g.val i j) h

def red : KO k ι →* GL ι 𝓀[k] :=
  (Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])).comp
    (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm.toMonoidHom

/- English proof (translation)
Use `set u := (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm x with hu`. Establish `h1 : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u = x.1`. Use `congrArg Subtype.val ((MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).apply_symm_apply x)` as an intermediate fact. Rewrite `this` using `[MonoidHom.ofInjective_apply]`. Conclude with `this`.

Establish `h2' : ((u.val r s : 𝒪[k]) : k) = x.1.val r s` using `by rw [← h1]; rfl`. Establish `h2 : u.val r s = ⟨x.1.val r s, h⟩` using `Subtype.ext h2'`. Use `show IsLocalRing.residue 𝒪[k] (u.val r s) = _`. Rewrite using `[h2]`.
-/
theorem red_val (x : KO k ι) (r s : ι) (h : x.1.val r s ∈ 𝒪[k]) :
    (red x).val r s = IsLocalRing.residue 𝒪[k] ⟨x.1.val r s, h⟩ := by
  set u := (MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).symm x with hu
  have h1 : Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u = x.1 := by
    have := congrArg Subtype.val ((MonoidHom.ofInjective (mapInt_injective (k := k) (ι := ι))).apply_symm_apply x)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  have h2' : ((u.val r s : 𝒪[k]) : k) = x.1.val r s := by rw [← h1]; rfl
  have h2 : u.val r s = ⟨x.1.val r s, h⟩ := Subtype.ext h2'
  show IsLocalRing.residue 𝒪[k] (u.val r s) = _
  rw [h2]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Use function extensionality and compare the values at `s`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct]`.
-/
theorem row_mul {R : Type} [CommRing R] (P Q : Matrix ι ι R) (t : ι) : (P * Q) t = Matrix.vecMul (P t) Q := by
  funext s; simp [Matrix.mul_apply, Matrix.vecMul, dotProduct]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `e1 : (M⁻¹).val = (M⁻¹ * N).val * (N⁻¹).val` using `by simp [mul_assoc]`. Rewrite using `[e1, row_mul, h, ← row_mul, one_mul]`. Introduce `h`.

Rewrite using `[Units.val_mul, row_mul, h, ← row_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]`.
-/
theorem row_inv_iff {R : Type} [CommRing R] (M N : GL ι R) (t : ι) :
    (M⁻¹ * N).val t = (1 : Matrix ι ι R) t ↔ (M⁻¹).val t = (N⁻¹).val t := by
  constructor
  · intro h
    have e1 : (M⁻¹).val = (M⁻¹ * N).val * (N⁻¹).val := by simp [mul_assoc]
    rw [e1, row_mul, h, ← row_mul, one_mul]
  · intro h
    rw [Units.val_mul, row_mul, h, ← row_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]

/- English proof (translation)
Rewrite using `[IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Establish `: a = ϖ * c` using `congrArg Subtype.val hc`. Rewrite using `[this, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]`.

Conclude with `c.2`. Introduce `h`. Use `⟨⟨_, h⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show a = ϖ * ((ϖ : k)⁻¹ * a)`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]`.
-/
theorem residue_eq_zero_iff_of_isUnif {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : k) (ha : a ∈ 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] ⟨a, ha⟩ = 0 ↔ (ϖ : k)⁻¹ * a ∈ 𝒪[k] := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have : a = ϖ * c := congrArg Subtype.val hc
    rw [this, ← mul_assoc, inv_mul_cancel₀ ϖ.ne_zero, one_mul]; exact c.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    show a = ϖ * ((ϖ : k)⁻¹ * a)
    rw [← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, hw, rfl⟩`. Simplify `hw` using `[mul_assoc]`. Introduce `h; exact ⟨_, h, by simp [mul_assoc]⟩`.
-/
theorem mem_map_conj_iff (g : GL ι k) (K : Subgroup (GL ι k)) (z : GL ι k) :
    z ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ K := by
  constructor
  · rintro ⟨w, hw, rfl⟩; simpa [mul_assoc] using hw
  · intro h; exact ⟨_, h, by simp [mul_assoc]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
/- English proof (translation)
Establish `hi : ((diagGL (Pi.mulSingle t ϖ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k)` using `rfl`. Rewrite using `[Units.val_mul, Units.val_mul, hi, diagGL_val, mul_diagonal, diagonal_mul]`. Apply the tactic sequence `by_cases hr : r = t <;> by_cases hs : s = t <;> simp [hr, hs, Pi.mulSingle_apply]`.
-/
theorem conj_diag_val (ϖ : kˣ) (t : ι) (z : GL ι k) (r s : ι) :
    ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s =
      (if r = t then (ϖ : k)⁻¹ else 1) * z.val r s * (if s = t then (ϖ : k) else 1) := by
  have hi : ((diagGL (Pi.mulSingle t ϖ))⁻¹).val = diagonal fun i => ((((Pi.mulSingle t ϖ : ι → kˣ) i)⁻¹ : kˣ) : k) := rfl
  rw [Units.val_mul, Units.val_mul, hi, diagGL_val, mul_diagonal, diagonal_mul]
  by_cases hr : r = t <;> by_cases hs : s = t <;> simp [hr, hs, Pi.mulSingle_apply]

/- English proof (translation)
Simplify using `only [conj_diag_val]`. Prove the components needed by the constructor for the conclusion. Introduce `h s hs`. Simplify `h t s` using `[hs]`. Introduce `h r s`.

Distinguish the cases in `hr : r = t`. Substitute `hr` using the available equality. Distinguish the cases in `hs : s = r`. Substitute `hs` using the available equality. Simplify using `only [if_true]`.

Rewrite using `[mul_comm, ← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]`. Conclude with `hz _ _`. Simplify `h s hs` using `[hs]`. Simplify using `only [hr, if_false, one_mul] split_ifs`. Conclude with `Subring.mul_mem _ (hz r s) hϖ.mem`.

Simplify using `using hz r s`.
-/
theorem conj_int_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (t : ι) (z : GL ι k) (hz : ∀ r s, z.val r s ∈ 𝒪[k]) :
    (∀ r s, ((diagGL (Pi.mulSingle t ϖ))⁻¹ * z * diagGL (Pi.mulSingle t ϖ)).val r s ∈ 𝒪[k]) ↔
      ∀ s, s ≠ t → (ϖ : k)⁻¹ * z.val t s ∈ 𝒪[k] := by
  simp only [conj_diag_val]
  constructor
  · intro h s hs
    simpa [hs] using h t s
  · intro h r s
    by_cases hr : r = t
    · subst hr
      by_cases hs : s = r
      · subst hs
        simp only [if_true]
        rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ ϖ.ne_zero, one_mul]; exact hz _ _
      · simpa [hs] using h s hs
    · simp only [hr, if_false, one_mul]
      split_ifs
      · exact Subring.mul_mem _ (hz r s) hϖ.mem
      · simpa using hz r s

/- English proof (translation)
The claim follows from `red_val (Subgroup.inclusion hHK z) r s h`.
-/
theorem red_incl_val {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) (z : H) (r s : ι) (h : (z : GL ι k).val r s ∈ 𝒪[k]) :
    (red (Subgroup.inclusion hHK z)).val r s = IsLocalRing.residue 𝒪[k] ⟨(z : GL ι k).val r s, h⟩ :=
  red_val (Subgroup.inclusion hHK z) r s h

/- English proof (translation)
Establish `hint` using `((mem_KO_iff _).1 (hHK z.2)).1 t s`. Rewrite using `[red_incl_val hHK z t s hint]`. Establish `e : (⟨z.1.val t s, hint⟩ : 𝒪[k]) = (1 : Matrix ι ι 𝒪[k]) t s`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show z.1.val t s = _`.

Rewrite using `[hrow z.1 z.2 s hs]`. Apply the tactic sequence `by_cases h : t = s <;> simp [Matrix.one_apply, h]`. Rewrite using `[e]`. Apply the tactic sequence `by_cases h : t = s <;> simp [Matrix.one_apply, h]`.
-/
theorem red_row_off {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι} {S : Finset ι}
    (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) (s : ι) (hs : s ∉ S) :
    (red (Subgroup.inclusion hHK z)).val t s = (1 : Matrix ι ι 𝓀[k]) t s := by
  have hint := ((mem_KO_iff _).1 (hHK z.2)).1 t s
  rw [red_incl_val hHK z t s hint]
  have e : (⟨z.1.val t s, hint⟩ : 𝒪[k]) = (1 : Matrix ι ι 𝒪[k]) t s := by
    apply Subtype.ext
    show z.1.val t s = _
    rw [hrow z.1 z.2 s hs]
    by_cases h : t = s <;> simp [Matrix.one_apply, h]
  rw [e]
  by_cases h : t = s <;> simp [Matrix.one_apply, h]

/- English proof (translation)
Use `set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ`. Establish `hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k]` using `fun w => ((mem_KO_iff _).1 (hHK w.2)).1`. Establish `key : ∀ w : H, (∀ s, s ≠ t → (ϖ : k)⁻¹ * (w : GL ι k).val t s ∈ 𝒪[k]) ↔ (ρ w).val t = (1 : Matrix ι ι 𝓀[k]) t`. Introduce `w`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use function extensionality and compare the values at `s`. Distinguish the cases in `hs : s = t`. Substitute `hs` using the available equality. Conclude with `red_row_off hHK hrow w s htS`.

Use `show (red (Subgroup.inclusion hHK w)).val t s = _`. Rewrite using `[red_incl_val hHK w t s (hint w t s), (residue_eq_zero_iff_of_isUnif hϖ _ _).2 (h s hs)]`. Simplify using `[Matrix.one_apply, Ne.symm hs]`. Introduce `h s hs`. Establish `h1` using `congrFun h s`.

Establish `h2 : (red (Subgroup.inclusion hHK w)).val t s = 0`. Rewrite using `[show (red (Subgroup.inclusion hHK w)).val t s = (ρ w).val t s from rfl, h1]`. Simplify using `[Matrix.one_apply, Ne.symm hs]`. Rewrite `h2` using `[red_incl_val hHK w t s (hint w t s)]`. Conclude with `(residue_eq_zero_iff_of_isUnif hϖ _ _).1 h2`.

Rewrite using `[mem_map_conj_iff, mem_KO_iff]`. Establish `hinv : ((diagGL (Pi.mulSingle t ϖ))⁻¹ * (z : GL ι k) * diagGL (Pi.mulSingle t ϖ))⁻¹ = (diagGL (Pi.mulSingle t ϖ))⁻¹ * ((z⁻¹ : H) : GL ι k) * diagGL (Pi.mulSingle t ϖ)`. Simplify using `[mul_assoc]`. Rewrite using `[hinv, conj_int_iff hϖ t _ (hint z), conj_int_iff hϖ t _ (hint z⁻¹)]`. Express the relevant statement in the definitionally equal form `_ ↔ (ρ z).val t = _`.

Rewrite using `[key z, key z⁻¹]`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h => h.1`. Introduce `h`. Use `⟨h, ?_⟩` and prove the remaining obligations.

Use `(row_inv_iff (1 : GL ι 𝓀[k]) (ρ z) t).1 (by simpa using h)` as an intermediate fact. Rewrite using `[map_inv, ← this]`. Simplify using the standard rewrite rules.
-/
theorem mem_conj_iff_row {ϖ : kˣ} (hϖ : IsUnif ϖ) {H : Subgroup (GL ι k)} (hHK : H ≤ KO k ι) {t : ι}
    {S : Finset ι} (htS : t ∉ S) (hrow : ∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) (z : H) :
    (z : GL ι k) ∈ (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom ↔
      (red (Subgroup.inclusion hHK z)).val t = (1 : Matrix ι ι 𝓀[k]) t := by
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1

  have key : ∀ w : H, (∀ s, s ≠ t → (ϖ : k)⁻¹ * (w : GL ι k).val t s ∈ 𝒪[k]) ↔ (ρ w).val t = (1 : Matrix ι ι 𝓀[k]) t := by
    intro w
    constructor
    · intro h
      funext s
      by_cases hs : s = t
      · subst hs; exact red_row_off hHK hrow w s htS
      · show (red (Subgroup.inclusion hHK w)).val t s = _
        rw [red_incl_val hHK w t s (hint w t s), (residue_eq_zero_iff_of_isUnif hϖ _ _).2 (h s hs)]
        simp [Matrix.one_apply, Ne.symm hs]
    · intro h s hs
      have h1 := congrFun h s
      have h2 : (red (Subgroup.inclusion hHK w)).val t s = 0 := by
        rw [show (red (Subgroup.inclusion hHK w)).val t s = (ρ w).val t s from rfl, h1]
        simp [Matrix.one_apply, Ne.symm hs]
      rw [red_incl_val hHK w t s (hint w t s)] at h2
      exact (residue_eq_zero_iff_of_isUnif hϖ _ _).1 h2
  rw [mem_map_conj_iff, mem_KO_iff]
  have hinv : ((diagGL (Pi.mulSingle t ϖ))⁻¹ * (z : GL ι k) * diagGL (Pi.mulSingle t ϖ))⁻¹ =
      (diagGL (Pi.mulSingle t ϖ))⁻¹ * ((z⁻¹ : H) : GL ι k) * diagGL (Pi.mulSingle t ϖ) := by
    simp [mul_assoc]
  rw [hinv, conj_int_iff hϖ t _ (hint z), conj_int_iff hϖ t _ (hint z⁻¹)]
  change _ ↔ (ρ z).val t = _
  rw [key z, key z⁻¹]
  constructor
  · exact fun h => h.1
  · intro h
    refine ⟨h, ?_⟩
    have := (row_inv_iff (1 : GL ι 𝓀[k]) (ρ z) t).1 (by simpa using h)
    rw [map_inv, ← this]; simp

/- English proof (translation)
Introduce `k _ _ _ _ ι _ _ ϖ hϖ t S htS H hHK hrow hel`. Use `set A := (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom with hA`. Use `set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ`. Establish `hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k]` using `fun w => ((mem_KO_iff _).1 (hHK w.2)).1`. Set `F : H → (S → 𝓀[k])` to `fun x s => (ρ x⁻¹).val t s`.

Establish `hF : ∀ x y : H, F x = F y ↔ ((x⁻¹ * y : H) : GL ι k) ∈ A`. Introduce `x y`. Rewrite using `[mem_conj_iff_row hϖ hHK htS hrow]`. Express the relevant statement in the definitionally equal form `_ ↔ (ρ (x⁻¹ * y)).val t = _`. Rewrite using `[map_mul, map_inv, row_inv_iff, ← map_inv, ← map_inv]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use function extensionality and compare the values at `s`. Distinguish the cases in `hs : s ∈ S`. Conclude with `congrFun h ⟨s, hs⟩`.

Rewrite using `[show (ρ x⁻¹).val t s = (red (Subgroup.inclusion hHK x⁻¹)).val t s from rfl, show (ρ y⁻¹).val t s = (red (Subgroup.inclusion hHK y⁻¹)).val t s from rfl, red_row_off hHK hrow _ s hs, red_row_off hHK hrow _ s hs]`. Introduce `h`. Use function extensionality and compare the values at `s`. Conclude with `congrFun h s.1`. Establish `hsurj : Function.Surjective F`.

Introduce `w`. Use `choose lift hlift using fun s : S => IsLocalRing.residue_surjective (R := 𝒪[k]) (w s)`. Set `y : ι → k` to `fun s => if h : s ∈ S then ((lift ⟨s, h⟩ : 𝒪[k]) : k) else 0`. Take `⟨z, hzH, hz⟩` from `hel y (fun s => by`. Distinguish the cases in `h : s ∈ S`.

Simplify using `only [y, h, dif_pos]`. Conclude with `(lift ⟨s, h⟩).2`. Simplify using `only [y, h, dif_neg, not_false_eq_true]`. Conclude with `Subring.zero_mem _)`. Use the proof step `(fun s hs => by simp [y, hs])`.

Use `⟨(⟨z, hzH⟩ : H)⁻¹, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `s`. Establish `hst : t ≠ s.1` using `fun h => htS (h ▸ s.2)`. Use `show (red (Subgroup.inclusion hHK ((⟨z, hzH⟩ : H)⁻¹)⁻¹)).val t s = w s`. Rewrite using `[inv_inv, red_incl_val hHK _ t s (hint _ t s)]`.

Establish `e : (⟨((⟨z, hzH⟩ : H) : GL ι k).val t s, hint _ t s⟩ : 𝒪[k]) = lift s`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show z.val t s = _`. Rewrite using `[hz]`. Simplify using `[y, Matrix.one_apply, hst, s.2]`.

Rewrite using `[e, hlift]`. Establish `hcard : Nat.card (H ⧸ A.subgroupOf H) = Nat.card (S → 𝓀[k])`. Use `Nat.card_congr (Equiv.ofBijective (Quotient.lift F fun a b hab => (hF a b).2 ?_) ⟨?_, ?_⟩)` and prove the remaining obligations. Use `QuotientGroup.leftRel_apply.mp hab` as an intermediate fact. Simplify `this` using `[Subgroup.mem_subgroupOf]`.

Introduce `a b`. Proceed by induction on `a using QuotientGroup.induction_on`. Proceed by induction on `b using QuotientGroup.induction_on`. Introduce `h`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Conclude with `(hF _ _).1 h`. Introduce `w`. Take `⟨x, hx⟩` from `hsurj w`. Conclude with `⟨QuotientGroup.mk x, hx⟩`. Rewrite using `[Subgroup.relIndex, Subgroup.index, hcard, Nat.card_fun, resCard, Nat.card_eq_fintype_card (α := S), Fintype.card_coe]`.
-/
theorem relIndex_rowCong : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (ϖ : kˣ), IsUnif ϖ → ∀ (t : ι) (S : Finset ι), t ∉ S →
    ∀ (H : Subgroup (GL ι k)), H ≤ KO k ι → (∀ x ∈ H, ∀ s, s ∉ S → x.val t s = (1 : Matrix ι ι k) t s) →
    (∀ y : ι → k, (∀ s, y s ∈ 𝒪[k]) → (∀ s, s ∉ S → y s = 0) →
      ∃ x ∈ H, x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0)) →
    ((KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom).relIndex H = resCard k ^ S.card := by
  intro k _ _ _ _ ι _ _ ϖ hϖ t S htS H hHK hrow hel
  set A := (KO k ι).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom with hA
  set ρ : H →* GL ι 𝓀[k] := red.comp (Subgroup.inclusion hHK) with hρ
  have hint : ∀ w : H, ∀ r s, (w : GL ι k).val r s ∈ 𝒪[k] := fun w => ((mem_KO_iff _).1 (hHK w.2)).1
  let F : H → (S → 𝓀[k]) := fun x s => (ρ x⁻¹).val t s
  have hF : ∀ x y : H, F x = F y ↔ ((x⁻¹ * y : H) : GL ι k) ∈ A := by
    intro x y
    rw [mem_conj_iff_row hϖ hHK htS hrow]
    change _ ↔ (ρ (x⁻¹ * y)).val t = _
    rw [map_mul, map_inv, row_inv_iff, ← map_inv, ← map_inv]
    constructor
    · intro h
      funext s
      by_cases hs : s ∈ S
      · exact congrFun h ⟨s, hs⟩
      · rw [show (ρ x⁻¹).val t s = (red (Subgroup.inclusion hHK x⁻¹)).val t s from rfl,
          show (ρ y⁻¹).val t s = (red (Subgroup.inclusion hHK y⁻¹)).val t s from rfl,
          red_row_off hHK hrow _ s hs, red_row_off hHK hrow _ s hs]
    · intro h
      funext s
      exact congrFun h s.1
  have hsurj : Function.Surjective F := by
    intro w
    choose lift hlift using fun s : S => IsLocalRing.residue_surjective (R := 𝒪[k]) (w s)
    let y : ι → k := fun s => if h : s ∈ S then ((lift ⟨s, h⟩ : 𝒪[k]) : k) else 0
    obtain ⟨z, hzH, hz⟩ := hel y (fun s => by
        by_cases h : s ∈ S
        · simp only [y, h, dif_pos]; exact (lift ⟨s, h⟩).2
        · simp only [y, h, dif_neg, not_false_eq_true]; exact Subring.zero_mem _)
      (fun s hs => by simp [y, hs])
    refine ⟨(⟨z, hzH⟩ : H)⁻¹, ?_⟩
    funext s
    have hst : t ≠ s.1 := fun h => htS (h ▸ s.2)
    show (red (Subgroup.inclusion hHK ((⟨z, hzH⟩ : H)⁻¹)⁻¹)).val t s = w s
    rw [inv_inv, red_incl_val hHK _ t s (hint _ t s)]
    have e : (⟨((⟨z, hzH⟩ : H) : GL ι k).val t s, hint _ t s⟩ : 𝒪[k]) = lift s := by
      apply Subtype.ext
      show z.val t s = _
      rw [hz]
      simp [y, Matrix.one_apply, hst, s.2]
    rw [e, hlift]
  have hcard : Nat.card (H ⧸ A.subgroupOf H) = Nat.card (S → 𝓀[k]) := by
    refine Nat.card_congr (Equiv.ofBijective (Quotient.lift F fun a b hab => (hF a b).2 ?_) ⟨?_, ?_⟩)
    · have := QuotientGroup.leftRel_apply.mp hab
      simpa [Subgroup.mem_subgroupOf] using this
    · intro a b
      induction a using QuotientGroup.induction_on
      induction b using QuotientGroup.induction_on
      intro h
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      exact (hF _ _).1 h
    · intro w
      obtain ⟨x, hx⟩ := hsurj w
      exact ⟨QuotientGroup.mk x, hx⟩
  rw [Subgroup.relIndex, Subgroup.index, hcard, Nat.card_fun, resCard, Nat.card_eq_fintype_card (α := S),
    Fintype.card_coe]

end GlobalTheory.DiagVol.RowIdx
