import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerfectPairingCount

variable {F : Type} [Field F]

/- English proof (translation)
Establish `h` using `linearIndependent_monoidHom G F`. Establish `hinj : Function.Injective (fun f : G →* Fˣ => (Units.coeHom F).comp f)`. Introduce `f g hfg`. Use extensionality with `x`. Conclude with `DFunLike.congr_fun hfg x`.

Conclude with `h.comp _ hinj`.
-/
theorem linearIndependent_unitsChar (G : Type) [Group G] :
    LinearIndependent F (fun (f : G →* Fˣ) => (fun g => ((f g : Fˣ) : F) : G → F)) := by
  have h := linearIndependent_monoidHom G F
  have hinj : Function.Injective (fun f : G →* Fˣ => (Units.coeHom F).comp f) := by
    intro f g hfg
    ext x
    exact DFunLike.congr_fun hfg x
  exact h.comp _ hinj

/- English proof (translation)
The claim follows from `(linearIndependent_unitsChar (F := F) G).finite`.
-/
theorem finite_unitsChar (G : Type) [Group G] [Finite G] : Finite (G →* Fˣ) :=
  (linearIndependent_unitsChar (F := F) G).finite

/- English proof (translation)
Use `haveI := finite_unitsChar (F := F) G`. Use `haveI := Fintype.ofFinite (G →* Fˣ)`. Use `haveI := Fintype.ofFinite G`. Establish `h` using `(linearIndependent_unitsChar (F := F) G).fintype_card_le_finrank`. Rewrite `h` using `[Module.finrank_fintype_fun_eq_card]`.

Simplify `h` using `[Nat.card_eq_fintype_card]`.
-/
theorem card_unitsChar_le (G : Type) [Group G] [Finite G] :
    Nat.card (G →* Fˣ) ≤ Nat.card G := by
  classical
  haveI := finite_unitsChar (F := F) G
  haveI := Fintype.ofFinite (G →* Fˣ)
  haveI := Fintype.ofFinite G
  have h := (linearIndependent_unitsChar (F := F) G).fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card] at h
  simpa [Nat.card_eq_fintype_card] using h

variable {A : Type} [CommGroup A] [Finite A]

/- English proof (translation)
Use `haveI := finite_unitsChar (F := F) (A ⧸ H)`. Set `φ : K → (A ⧸ H →* Fˣ)` to `fun k => QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)`. Establish `hφ : Function.Injective φ`. Introduce `k k' hkk`. Establish `h1 : E k = E k'`.

Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `b`. Use `DFunLike.congr_fun hkk (QuotientGroup.mk b)` as an intermediate fact. Conclude with `this`. Establish `h2 : (k : A) * (k' : A)⁻¹ = 1`.

Apply `hE` to reduce the goal to its premises. Introduce `b`. Rewrite using `[map_mul, map_inv, h1, mul_inv_cancel]`. Both sides reduce to the same expression. Conclude with `Subtype.ext (mul_inv_eq_one.mp h2)`.

Establish `h3 : Nat.card K ≤ Nat.card (A ⧸ H)` using `(Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)`. Rewrite using `[Subgroup.card_eq_card_quotient_mul_card_subgroup H]`. Conclude with `Nat.mul_le_mul_right _ h3`.
-/
theorem card_ker_mul_le (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (H K : Subgroup A) (hK : ∀ k ∈ K, ∀ h ∈ H, E k h = 1) :
    Nat.card K * Nat.card H ≤ Nat.card A := by
  haveI := finite_unitsChar (F := F) (A ⧸ H)
  let φ : K → (A ⧸ H →* Fˣ) := fun k =>
    QuotientGroup.lift H (E k) (fun h hh => hK k k.2 h hh)
  have hφ : Function.Injective φ := by
    intro k k' hkk
    have h1 : E k = E k' := by
      apply MonoidHom.ext
      intro b
      have := DFunLike.congr_fun hkk (QuotientGroup.mk b)
      exact this
    have h2 : (k : A) * (k' : A)⁻¹ = 1 := by
      apply hE
      intro b
      rw [map_mul, map_inv, h1, mul_inv_cancel]
      rfl
    exact Subtype.ext (mul_inv_eq_one.mp h2)
  have h3 : Nat.card K ≤ Nat.card (A ⧸ H) :=
    (Nat.card_le_card_of_injective φ hφ).trans (card_unitsChar_le _)
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup H]
  exact Nat.mul_le_mul_right _ h3

/- English proof (translation)
Establish `h` using `card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by`. Use `DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k` as an intermediate fact. Simplify using `using this)`. Rewrite `h` using `[Subgroup.card_top]`. Establish `hpos : 0 < Nat.card A` using `Nat.card_pos`.

Establish `h1 : Nat.card E.flip.ker ≤ 1`. Establish `: Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1` using `by simpa using h`. Conclude with `Nat.le_of_mul_le_mul_left this hpos`. Establish `h2 : E.flip.ker = ⊥` using `Subgroup.card_le_one_iff_eq_bot _ |>.mp h1`. Establish `h3 : b ∈ E.flip.ker`.

Rewrite using `[MonoidHom.mem_ker]`. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `a`. Simplify using `using hb a`. Rewrite `h3` using `[h2]`.

Conclude with `Subgroup.mem_bot.mp h3`.
-/
theorem right_nondegenerate (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (b : A) (hb : ∀ a, E a b = 1) : b = 1 := by
  have h := card_ker_mul_le E hE E.flip.ker ⊤ (fun k _ h hh => by
    have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hh) k
    simpa using this)
  rw [Subgroup.card_top] at h
  have hpos : 0 < Nat.card A := Nat.card_pos
  have h1 : Nat.card E.flip.ker ≤ 1 := by
    have : Nat.card A * Nat.card E.flip.ker ≤ Nat.card A * 1 := by simpa using h
    exact Nat.le_of_mul_le_mul_left this hpos
  have h2 : E.flip.ker = ⊥ := Subgroup.card_le_one_iff_eq_bot _ |>.mp h1
  have h3 : b ∈ E.flip.ker := by
    rw [MonoidHom.mem_ker]
    apply MonoidHom.ext
    intro a
    simpa using hb a
  rw [h2] at h3
  exact Subgroup.mem_bot.mp h3

/- English proof (translation)
Set `R : A →* (H →* Fˣ)` to `{ toFun := fun a => (E a).comp H.subtype map_one' := by apply MonoidHom.ext; intro h; simp map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }`. Establish `hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1`. Introduce `x`. Rewrite using `[MonoidHom.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `hx h hh`. Conclude with `DFunLike.congr_fun hx ⟨h, hh⟩`. Introduce `hx`. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `h`.

Conclude with `hx h h.2`. Establish `hle : T ≤ R.ker` using `fun t ht => (hR t).mpr (hTH t ht)`. Establish `hHpos : 0 < Nat.card H` using `Nat.card_pos`. Establish `hTpos : 0 < Nat.card T` using `Nat.card_pos`. Establish `hcard : Nat.card R.ker ≤ Nat.card T`.

Use `card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)` as an intermediate fact. Rewrite `this` using `[← hc]`. Conclude with `Nat.le_of_mul_le_mul_right this hHpos`. Establish `heq : T = R.ker` using `Subgroup.eq_of_le_of_card_ge hle hcard`. Use `⟨fun x => by rw [← hR, heq], ?_⟩` and prove the remaining obligations.

Use `haveI := finite_unitsChar (F := F) H`. Establish `hrange : Nat.card R.range = Nat.card H`. Establish `h1` using `Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker`. Rewrite `h1` using `[Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc, mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_right hTpos h1).symm`.

Establish `htop : R.range = ⊤`. Apply `Subgroup.eq_of_le_of_card_ge le_top` to reduce the goal to its premises. Rewrite using `[Subgroup.card_top, hrange]`. Conclude with `card_unitsChar_le _`. Introduce `χ`.

Establish `: χ ∈ R.range` using `by rw [htop]; trivial`. Take `⟨x, hx⟩` from `this`. Conclude with `⟨x, fun h => DFunLike.congr_fun hx h⟩`.
-/
theorem one_side (E : A →* (A →* Fˣ)) (hE : ∀ a, (∀ b, E a b = 1) → a = 1)
    (T H : Subgroup A) (hTH : ∀ t ∈ T, ∀ h ∈ H, E t h = 1)
    (hc : Nat.card T * Nat.card H = Nat.card A) :
    (∀ x, (∀ h ∈ H, E x h = 1) ↔ x ∈ T) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, E x h = χ h) := by
  let R : A →* (H →* Fˣ) :=
    { toFun := fun a => (E a).comp H.subtype
      map_one' := by apply MonoidHom.ext; intro h; simp
      map_mul' := by intro a a'; apply MonoidHom.ext; intro h; simp }
  have hR : ∀ x, x ∈ R.ker ↔ ∀ h ∈ H, E x h = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx h hh
      exact DFunLike.congr_fun hx ⟨h, hh⟩
    · intro hx
      apply MonoidHom.ext
      intro h
      exact hx h h.2
  have hle : T ≤ R.ker := fun t ht => (hR t).mpr (hTH t ht)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hcard : Nat.card R.ker ≤ Nat.card T := by
    have := card_ker_mul_le E hE H R.ker (fun k hk => (hR k).mp hk)
    rw [← hc] at this
    exact Nat.le_of_mul_le_mul_right this hHpos
  have heq : T = R.ker := Subgroup.eq_of_le_of_card_ge hle hcard
  refine ⟨fun x => by rw [← hR, heq], ?_⟩
  haveI := finite_unitsChar (F := F) H
  have hrange : Nat.card R.range = Nat.card H := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup R.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange R).toEquiv, ← heq, ← hc,
      mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right hTpos h1).symm
  have htop : R.range = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    rw [Subgroup.card_top, hrange]
    exact card_unitsChar_le _
  intro χ
  have : χ ∈ R.range := by rw [htop]; trivial
  obtain ⟨x, hx⟩ := this
  exact ⟨x, fun h => DFunLike.congr_fun hx h⟩

end GlobalTheory.PerfectPairingCount

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ A _ _ e h1 h2 h3 T H hTH hc`. Set `E : A →* (A →* Fˣ)` to `MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by`. Apply `MonoidHom.ext` to reduce the goal to its premises. Introduce `b`. Conclude with `h1 a a' b)`.

Establish `hE : ∀ a, (∀ b, E a b = 1) → a = 1` using `h3`. Establish `hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1` using `fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb`. Take `⟨a1, a2⟩` from `PerfectPairingCount.one_side E hE T H hTH hc`. Take `⟨b1, b2⟩` from `PerfectPairingCount.one_side E.flip hE' H T (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])`. Conclude with `⟨a1, b1, a2, b2⟩`.
-/
theorem perfectPairing_orthogonal_of_card :
    ∀ (F : Type) [Field F] (A : Type) [CommGroup A] [Finite A] (e : A → A → Fˣ), (∀ a a' b, e (a * a') b = e a b * e a' b) → (∀ a b b', e a (b * b') = e a b * e a b') → (∀ a, (∀ b, e a b = 1) → a = 1) → ∀ T H : Subgroup A, (∀ t ∈ T, ∀ h ∈ H, e t h = 1) → Nat.card T * Nat.card H = Nat.card A → (∀ x, (∀ h ∈ H, e x h = 1) ↔ x ∈ T) ∧ (∀ x, (∀ t ∈ T, e t x = 1) ↔ x ∈ H) ∧ (∀ χ : H →* Fˣ, ∃ x, ∀ h : H, e x h = χ h) ∧ (∀ χ : T →* Fˣ, ∃ x, ∀ t : T, e t x = χ t) := by
  intro F _ A _ _ e h1 h2 h3 T H hTH hc
  let E : A →* (A →* Fˣ) :=
    MonoidHom.mk' (fun a => MonoidHom.mk' (e a) (h2 a)) (fun a a' => by
      apply MonoidHom.ext
      intro b
      exact h1 a a' b)
  have hE : ∀ a, (∀ b, E a b = 1) → a = 1 := h3
  have hE' : ∀ b, (∀ a, E.flip b a = 1) → b = 1 :=
    fun b hb => PerfectPairingCount.right_nondegenerate E hE b hb
  obtain ⟨a1, a2⟩ := PerfectPairingCount.one_side E hE T H hTH hc
  obtain ⟨b1, b2⟩ := PerfectPairingCount.one_side E.flip hE' H T
    (fun h hh t ht => hTH t ht h hh) (by rw [mul_comm, hc])
  exact ⟨a1, b1, a2, b2⟩

end GlobalTheory
