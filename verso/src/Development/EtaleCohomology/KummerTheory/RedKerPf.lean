import Development.EtaleCohomology.KummerTheory.BockCut

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.RedKerPf

open LateralTheory.KummerTheory.BockCut

/- English proof (translation)
Take `⟨S, hS, hh⟩` from `h`. Establish `h1` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)`. Conclude with `(h1 S hS).isSeparatedFor.ext (fun V g hg => hh V g hg)`.
-/
theorem sepLoc {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (y z : Sec F U)
    (h : Loc U fun V g => Sec.res g y = Sec.res g z) : y = z := by
  obtain ⟨S, hS, hh⟩ := h
  have h1 := (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget _ F.obj (forget (ModuleCat.{1} (ULift.{1} R)))).1 F.cond)
  exact (h1 S hS).isSeparatedFor.ext (fun V g hg => hh V g hg)

/- English proof (translation)
Use `sepLoc y 0 (hL.2.1 U _ _ h fun V g hg => ?_)` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `(map_zero _).symm`.
-/
theorem locZero {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure)
    (y : Sec F U) (h : Loc U fun V g => Sec.res g y = 0) : y = 0 := by
  refine sepLoc y 0 (hL.2.1 U _ _ h fun V g hg => ?_)
  rw [hg]; exact (map_zero _).symm

/- English proof (translation)
The claim follows from `sepLoc y 0 (hL.2.2.2.2.2.2 V _)`.
-/
theorem secEmpty {R : Type} [CommRing R] {F : Shv R} {V : Scheme.{0}} [IsEmpty V]
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) (y : Sec F V) : y = 0 :=
  sepLoc y 0 (hL.2.2.2.2.2.2 V _)

/- English proof (translation)
The claim follows from `(congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)).symm`.
-/
theorem resMap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) :=
  (congrArg (fun f => (ModuleCat.Hom.hom f) x) (φ.hom.naturality g.op)).symm

/- English proof (translation)
The claim follows from `map_nsmul _ _ _`.
-/
theorem resNsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (x : Sec F U) :
    Sec.res g (n • x) = n • Sec.res g x := map_nsmul _ _ _

/- English proof (translation)
The claim follows from `map_nsmul _ _ _`.
-/
theorem mapNsmul {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (n : ℕ) (x : Sec F U) :
    Sec.map φ (n • x) = n • Sec.map φ x := map_nsmul _ _ _

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]`. Establish `: ((q : ℕ) : ULift.{1} (ZMod q)) = 0` using `by ext; simp`. Rewrite using `[this, zero_smul]`.
-/
theorem killTw {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (tw q i) U) : q • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q : ℕ) : ULift.{1} (ZMod q)) = 0 := by ext; simp
  rw [this, zero_smul]

/- English proof (translation)
The claim follows from `killTw (i := i) x`.
-/
theorem kill {q : ℕ} {i : ℤ} {U : Scheme.{0}} (x : Sec (TZ q i) U) : q • x = 0 := killTw (i := i) x

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `(hP Q Γ(V, ⊤)).2.2.2.2.2 q ⟨e, by rw [hQ, mul_comm]⟩ ζ`. Rewrite using `[mapNsmul, hπ V ζ ξ hξ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `(hT q i).2.2.1 V ξ c h`.

Introduce and unpack `⟨k, rfl⟩`. Rewrite using `[mul_comm, mul_smul, kill, smul_zero]`.
-/
theorem mapGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (Q e q : ℕ) [NeZero Q] [NeZero q] (hQ : Q = e * q) (i : ℤ) (π : TZ Q i ⟶ TZ q i) (hπ : IsRed Q q i π)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    Sec.map π (c • genZ i ζ) = 0 ↔ q ∣ c := by
  obtain ⟨ξ, hξ⟩ := (hP Q Γ(V, ⊤)).2.2.2.2.2 q ⟨e, by rw [hQ, mul_comm]⟩ ζ
  rw [mapNsmul, hπ V ζ ξ hξ]
  constructor
  · intro h; exact (hT q i).2.2.1 V ξ c h
  · rintro ⟨k, rfl⟩
    rw [mul_comm, mul_smul, kill, smul_zero]

/- English proof (translation)
Establish `he : 0 < e`. Break down `Nat.eq_zero_or_pos e with h | h` into its components or cases. Conclude with `absurd (by rw [hQ, h, zero_mul]) (NeZero.ne Q)`. Conclude with `h`. Rewrite using `[← mul_smul]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `(hT Q i).2.2.1 V ζ (e * c) h` as an intermediate fact. Rewrite `this` using `[hQ]`. Conclude with `(Nat.mul_dvd_mul_iff_left he).1 this`.

Introduce and unpack `⟨k, rfl⟩`. Establish `: e * (q * k) = Q * k` using `by rw [hQ]; ring`. Rewrite using `[this, mul_comm, mul_smul, kill, smul_zero]`.
-/
theorem eGen (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated)
    (Q e q : ℕ) [NeZero Q] (hQ : Q = e * q) (i : ℤ)
    (V : Scheme.{0}) [Nonempty V] (ζ : Prim Q Γ(V, ⊤)) (c : ℕ) :
    e • (c • genZ i ζ) = 0 ↔ q ∣ c := by
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · exact absurd (by rw [hQ, h, zero_mul]) (NeZero.ne Q)
    · exact h
  rw [← mul_smul]
  constructor
  · intro h
    have := (hT Q i).2.2.1 V ζ (e * c) h
    rw [hQ] at this
    exact (Nat.mul_dvd_mul_iff_left he).1 this
  · rintro ⟨k, rfl⟩
    have : e * (q * k) = Q * k := by rw [hQ]; ring
    rw [this, mul_comm, mul_smul, kill, smul_zero]

/- English proof (translation)
Introduce `Q e q _ hQ i π hπ U y`. Use `haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (by rw [hQ, mul_zero])⟩`. Establish `L` using `(hT Q i).1 U y`. Establish `key : Sec.map π y = 0 → Loc U fun V g => Sec.res g y = 0 ∨ (Nonempty V ∧ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ), q ∣ c ∧ Sec.res (F` using `TZ Q i) g y = c • genZ i ζ) ∨ IsEmpty V := by`. Introduce `h0`.

Use `hL.2.1 U _ _ L fun V g hg => ?_` and prove the remaining obligations. Break down `hg with hg | ⟨ζ, c, hc⟩` into its components or cases. Conclude with `Or.inl hg`. Break down `isEmpty_or_nonempty V with hV | hV` into its components or cases. Conclude with `Or.inr (Or.inr hV)`.

Use `Or.inr (Or.inl ⟨hV, ζ, c, ?_, hc⟩)` and prove the remaining obligations. Establish `h1 : Sec.map π (Sec.res (F` using `TZ Q i) g y) = 0 := by rw [← resMap, h0]; exact map_zero _`. Establish `hc' : Sec.res (F` using `TZ Q i) g y = c • genZ i ζ := hc`. Rewrite `h1` using `[hc']`. Conclude with `(mapGen hT hP Q e q hQ i π hπ V ζ c).1 h1`.

Use `⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun h0 => ?_⟩` and prove the remaining obligations. Use `locZero hL _ (hL.2.1 U _ _ (key h0) fun V g hg => ?_)` and prove the remaining obligations. Rewrite using `[resNsmul]`. Break down `hg with hg | ⟨hV, ζ, c, hc, hg⟩ | hV` into its components or cases. Rewrite using `[hg]`.

Conclude with `smul_zero _`. Rewrite using `[hg]`. Conclude with `(eGen hT Q e q hQ i V ζ c).2 hc`. Conclude with `secEmpty hL _`. Use `locZero hL _ (hL.2.1 U _ _ L fun V g hg => ?_)` and prove the remaining obligations.

Rewrite using `[resMap]`. Break down `hg with hg | ⟨ζ, c, hc⟩` into its components or cases. Establish `hg' : Sec.res (F` using `TZ Q i) g y = 0 := hg`. Rewrite using `[hg']`. Conclude with `map_zero _`.

Break down `isEmpty_or_nonempty V with hV | hV` into its components or cases. Conclude with `secEmpty hL _`. Establish `hc' : Sec.res (F` using `TZ Q i) g y = c • genZ i ζ := hc`. Establish `h1 : e • Sec.res (F` using `TZ Q i) g y = 0 := by rw [← resNsmul, h0]; exact map_zero _`. Rewrite `h1`, the goal using `[hc']`.

Conclude with `(mapGen hT hP Q e q hQ i π hπ V ζ c).2 ((eGen hT Q e q hQ i V ζ c).1 h1)`. Use `hL.2.1 U _ _ (key h0) fun V g hg => ?_` and prove the remaining obligations. Break down `hg with hg | ⟨hV, ζ, c, ⟨k, rfl⟩, hg⟩ | hV` into its components or cases. Conclude with `⟨0, by rw [hg]; exact smul_zero _⟩`. Conclude with `⟨k • genZ i ζ, by rw [hg, ← mul_smul]⟩`.

Conclude with `⟨0, by rw [smul_zero]; exact (secEmpty hL _).symm⟩`.
-/
theorem RedKer_of (hT : LateralTheory.EtaleFoundations.EtaleTateTwistSectionsLocallyGenerated) (hP : LateralTheory.EtaleFoundations.PrimitiveRootsOfUnityBasicIdentities)
    (hL : LateralTheory.EtaleFoundations.EtaleLocalPropertyBasicClosure) : RedKer := by
  intro Q e q _ hQ i π hπ U y
  haveI : NeZero q := ⟨by rintro rfl; exact NeZero.ne Q (by rw [hQ, mul_zero])⟩
  have L := (hT Q i).1 U y

  have key : Sec.map π y = 0 → Loc U fun V g => Sec.res g y = 0 ∨ (Nonempty V ∧ ∃ (ζ : Prim Q Γ(V, ⊤)) (c : ℕ),
      q ∣ c ∧ Sec.res (F := TZ Q i) g y = c • genZ i ζ) ∨ IsEmpty V := by
    intro h0
    refine hL.2.1 U _ _ L fun V g hg => ?_
    rcases hg with hg | ⟨ζ, c, hc⟩
    · exact Or.inl hg
    rcases isEmpty_or_nonempty V with hV | hV
    · exact Or.inr (Or.inr hV)
    refine Or.inr (Or.inl ⟨hV, ζ, c, ?_, hc⟩)
    have h1 : Sec.map π (Sec.res (F := TZ Q i) g y) = 0 := by rw [← resMap, h0]; exact map_zero _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    rw [hc'] at h1
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).1 h1
  refine ⟨⟨fun h0 => ?_, fun h0 => ?_⟩, fun h0 => ?_⟩
  · refine locZero hL _ (hL.2.1 U _ _ (key h0) fun V g hg => ?_)
    rw [resNsmul]
    rcases hg with hg | ⟨hV, ζ, c, hc, hg⟩ | hV
    · rw [hg]; exact smul_zero _
    · rw [hg]; exact (eGen hT Q e q hQ i V ζ c).2 hc
    · exact secEmpty hL _
  · refine locZero hL _ (hL.2.1 U _ _ L fun V g hg => ?_)
    rw [resMap]
    rcases hg with hg | ⟨ζ, c, hc⟩
    · have hg' : Sec.res (F := TZ Q i) g y = 0 := hg
      rw [hg']; exact map_zero _
    rcases isEmpty_or_nonempty V with hV | hV
    · exact secEmpty hL _
    have hc' : Sec.res (F := TZ Q i) g y = c • genZ i ζ := hc
    have h1 : e • Sec.res (F := TZ Q i) g y = 0 := by rw [← resNsmul, h0]; exact map_zero _
    rw [hc'] at h1 ⊢
    exact (mapGen hT hP Q e q hQ i π hπ V ζ c).2 ((eGen hT Q e q hQ i V ζ c).1 h1)
  · refine hL.2.1 U _ _ (key h0) fun V g hg => ?_
    rcases hg with hg | ⟨hV, ζ, c, ⟨k, rfl⟩, hg⟩ | hV
    · exact ⟨0, by rw [hg]; exact smul_zero _⟩
    · exact ⟨k • genZ i ζ, by rw [hg, ← mul_smul]⟩
    · exact ⟨0, by rw [smul_zero]; exact (secEmpty hL _).symm⟩

end LateralTheory.KummerTheory.RedKerPf
