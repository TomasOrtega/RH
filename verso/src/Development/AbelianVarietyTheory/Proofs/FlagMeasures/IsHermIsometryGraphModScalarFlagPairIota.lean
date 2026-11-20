import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.ModIdent

section Flag

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

/- English proof (translation)
Establish `: F.X ≤ LinearMap.ker (H.B.flip w)`. Unfold `FlagD.X FlagD.Xa`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, -, rfl⟩`. Conclude with `hw b`.

Conclude with `this hx`.
-/
theorem orth_of_mem_X (F : FlagD H r) {w : V} (hw : ∀ a : Fin r, H.B (F.e a.castSucc) w = 0) {x : V}
    (hx : x ∈ F.X) : H.B x w = 0 := by
  have : F.X ≤ LinearMap.ker (H.B.flip w) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    exact hw b
  exact this hx

/- English proof (translation)
Rewrite using `[← H.herm, h, star_zero]`.
-/
theorem orth_symm {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

/- English proof (translation)
The claim follows from `orth_of_mem_X F (fun a => orth_symm (orth_of_mem_X F (fun b => F.iso b a) hy)) hx`.
-/
theorem X_iso (F : FlagD H r) {x y : V} (hx : x ∈ F.X) (hy : y ∈ F.X) : H.B x y = 0 :=
  orth_of_mem_X F (fun a => orth_symm (orth_of_mem_X F (fun b => F.iso b a) hy)) hx

/- English proof (translation)
The claim follows from `orth_of_mem_X F F.zperp hx`.
-/
theorem pairing_isotropicSpan_lastVector (F : FlagD H r) {x : V} (hx : x ∈ F.X) : H.B x F.z = 0 :=
  orth_of_mem_X F F.zperp hx

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hb => Nat.lt_succ_of_lt hb)`.
-/
theorem Xa_le_succ (F : FlagD H r) (n : ℕ) : F.Xa n ≤ F.Xa (n + 1) :=
  Submodule.span_mono (Set.image_mono fun _ hb => Nat.lt_succ_of_lt hb)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨a, h, rfl⟩`.
-/
theorem e_mem_Xa (F : FlagD H r) (a : Fin r) {n : ℕ} (h : a.val < n) : F.e a.castSucc ∈ F.Xa n :=
  Submodule.subset_span ⟨a, h, rfl⟩

/- English proof (translation)
Establish `: F.Xa (a.val + 1) ≤ F.Xa a.val ⊔ Submodule.span K {F.e a.castSucc}` using `by conv_lhs => unfold FlagD.Xa`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Break down `Nat.lt_succ_iff_lt_or_eq.1 hb with h | h` into its components or cases. Conclude with `Submodule.mem_sup_left (e_mem_Xa F b h)`.

Take `rfl : b = a` from `Fin.ext h`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 (this hx)`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hv`. Conclude with `⟨t, by simpa using hu⟩`.
-/
theorem exists_coeff (F : FlagD H r) (a : Fin r) {x : V} (hx : x ∈ F.Xa (a.val + 1)) :
    ∃ t : K, x - t • F.e a.castSucc ∈ F.Xa a.val := by
  have : F.Xa (a.val + 1) ≤ F.Xa a.val ⊔ Submodule.span K {F.e a.castSucc} := by
    conv_lhs => unfold FlagD.Xa
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hb with h | h
    · exact Submodule.mem_sup_left (e_mem_Xa F b h)
    · obtain rfl : b = a := Fin.ext h
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 (this hx)
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
  exact ⟨t, by simpa using hu⟩

/- English proof (translation)
Simplify using `[FlagD.Xa]`.
-/
theorem Xa_zero (F : FlagD H r) : F.Xa 0 = ⊥ := by
  simp [FlagD.Xa]

/- English proof (translation)
Unfold `V0`. Rewrite using `[sup_comm F'.X, Set.pair_comm]`.
-/
theorem jointSpan_comm (F F' : FlagD H r) : V0 F' F = V0 F F' := by
  unfold V0
  rw [sup_comm F'.X, Set.pair_comm]

/- English proof (translation)
The claim follows from `le_sup_of_le_left le_sup_left`.
-/
theorem isotropicSpan_le_jointSpan_left (F F' : FlagD H r) : F.X ≤ V0 F F' := le_sup_of_le_left le_sup_left

/- English proof (translation)
The claim follows from `le_sup_left`.
-/
theorem hermFlagPair_isotropic_sup_le_commonSpace (F F' : FlagD H r) : F.X ⊔ F'.X ≤ V0 F F' := le_sup_left

/- English proof (translation)
The claim follows from `Submodule.mem_sup_right (Submodule.subset_span (by simp))`.
-/
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

end Flag

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
/- English proof (translation)
Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]`.
-/
theorem nsmul_eq (g : ℕ) (v : V) : (g : 𝓞 K) • v = (g : K) • v := by
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

omit [NumberField K] [StarRing K] in
/- English proof (translation)
Unfold `smulLat`. Rewrite using `[Submodule.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `⟨m, hm, nsmul_eq g m⟩`.

Introduce and unpack `⟨m, hm, rfl⟩`. Conclude with `⟨m, hm, nsmul_eq g m⟩`.
-/
theorem mem_smulLat (g : ℕ) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ smulLat (g : 𝓞 K) M ↔ ∃ m ∈ M, y = (g : K) • m := by
  unfold smulLat
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, nsmul_eq g m⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, nsmul_eq g m⟩

omit [NumberField K] [StarRing K] in
/- English proof (translation)
Rewrite using `[← nsmul_eq]`. Conclude with `M.smul_mem _ hm`.
-/
theorem gsmul_mem (g : ℕ) {M : Submodule (𝓞 K) V} {m : V} (hm : m ∈ M) : (g : K) • m ∈ M := by
  rw [← nsmul_eq]; exact M.smul_mem _ hm

omit [NumberField K] in
/- English proof (translation)
Unfold `flagPairDefinitePartLattice latL uPerp wSp`. Simplify using `only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_perp_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨-, h⟩, h'⟩`. Take `⟨l, hl, x, hx, rfl⟩` from `Submodule.mem_sup.1 h`.

Conclude with `⟨h', l, hl, by simpa using hx⟩`. Introduce and unpack `⟨h, l, hl, hx⟩`. Conclude with `⟨⟨fun v hv => h v (hermFlagPair_isotropic_sup_le_commonSpace F F' hv), Submodule.mem_sup.2 ⟨l, hl, y - l, hx, by abel⟩⟩, h⟩`.
-/
theorem mem_perp_lattice_flag_iff (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (y : V) :
    y ∈ flagPairDefinitePartLattice F F' Λ ↔ (∀ v ∈ V0 F F', H.B y v = 0) ∧ ∃ l ∈ Λ, y - l ∈ F.X := by
  unfold flagPairDefinitePartLattice latL uPerp wSp
  simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, mem_perp_iff]
  constructor
  · rintro ⟨⟨-, h⟩, h'⟩
    obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.1 h
    exact ⟨h', l, hl, by simpa using hx⟩
  · rintro ⟨h, l, hl, hx⟩
    exact ⟨⟨fun v hv => h v (hermFlagPair_isotropic_sup_le_commonSpace F F' hv), Submodule.mem_sup.2 ⟨l, hl, y - l, hx, by abel⟩⟩, h⟩

omit [NumberField K] in
/- English proof (translation)
Unfold `iotaGraph`. Rewrite using `[Submodule.mem_inf, Submodule.mem_prod, and_assoc]`. Use `and_congr_right fun _ => and_congr_right fun _ => ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Take `⟨⟨l', l⟩, ⟨⟨hl', hl⟩, hd⟩, ⟨x', x⟩, ⟨hx', hx⟩, he⟩` from `Submodule.mem_sup.1 h`. Take `⟨rfl, rfl⟩` from `Prod.mk.inj he`. Establish `hd' : l - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)` using `hd`. Take `⟨u, hu, v, ⟨-, hv⟩, huv⟩` from `Submodule.mem_sup.1 hd'`. Take `⟨m, hm, rfl⟩` from `(mem_smulLat g Λ u).1 hu`.

Use `⟨l', hl', m, hm, by simpa using hx', ?_⟩` and prove the remaining obligations. Establish `: l + x - (l' + (g : K) • m) = v + x`. Rewrite `huv` using `[eq_sub_iff_add_eq]`. Rewrite using `[← huv]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this]`. Conclude with `F.X.add_mem hv hx`. Introduce and unpack `⟨l', hl', m, hm, h', h⟩`. Use `Submodule.mem_sup.2 ⟨(l', l' + (g : K) • m), ⟨⟨hl', Λ.add_mem hl' (gsmul_mem g hm)⟩, ?_⟩, (y' - l', y - (l' + (g : K) • m)), ⟨h', h⟩, by simp⟩` and prove the remaining obligations. Use `show l' + (g : K) • m - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)`.

Conclude with `Submodule.mem_sup_left ((mem_smulLat g Λ _).2 ⟨m, hm, by abel⟩)`.
-/
theorem mem_iota (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (g : ℕ) (y' y : V) :
    (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K) ↔ y' ∈ flagPairDefinitePartLattice F' F Λ ∧ y ∈ flagPairDefinitePartLattice F F' Λ ∧
      ∃ l' ∈ Λ, ∃ m ∈ Λ, y' - l' ∈ F'.X ∧ y - (l' + (g : K) • m) ∈ F.X := by
  unfold iotaGraph
  rw [Submodule.mem_inf, Submodule.mem_prod, and_assoc]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h
    obtain ⟨⟨l', l⟩, ⟨⟨hl', hl⟩, hd⟩, ⟨x', x⟩, ⟨hx', hx⟩, he⟩ := Submodule.mem_sup.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    have hd' : l - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X) := hd
    obtain ⟨u, hu, v, ⟨-, hv⟩, huv⟩ := Submodule.mem_sup.1 hd'
    obtain ⟨m, hm, rfl⟩ := (mem_smulLat g Λ u).1 hu
    refine ⟨l', hl', m, hm, by simpa using hx', ?_⟩
    have : l + x - (l' + (g : K) • m) = v + x := by
      rw [eq_sub_iff_add_eq] at huv
      rw [← huv]; abel
    rw [this]
    exact F.X.add_mem hv hx
  · rintro ⟨l', hl', m, hm, h', h⟩
    refine Submodule.mem_sup.2 ⟨(l', l' + (g : K) • m), ⟨⟨hl', Λ.add_mem hl' (gsmul_mem g hm)⟩, ?_⟩,
      (y' - l', y - (l' + (g : K) • m)), ⟨h', h⟩, by simp⟩
    show l' + (g : K) • m - l' ∈ smulLat (g : 𝓞 K) Λ ⊔ (Λ ⊓ rs (𝓞 K) F.X)
    exact Submodule.mem_sup_left ((mem_smulLat g Λ _).2 ⟨m, hm, by abel⟩)

omit [NumberField K] in
/- English proof (translation)
Rewrite `h`, the goal using `[mem_iota]`. Take `⟨h1, h2, l', hl', m, hm, h3, h4⟩` from `h`. Use `⟨h2, h1, _, Λ.add_mem hl' (gsmul_mem g hm), -m, Λ.neg_mem hm, h4, by simpa using h3⟩` and prove the remaining obligations.
-/
theorem iota_swap {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} {y' y : V}
    (h : (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K)) : (y, y') ∈ iotaGraph F' F Λ (g : 𝓞 K) := by
  rw [mem_iota] at h ⊢
  obtain ⟨h1, h2, l', hl', m, hm, h3, h4⟩ := h
  refine ⟨h2, h1, _, Λ.add_mem hl' (gsmul_mem g hm), -m, Λ.neg_mem hm, h4, by simpa using h3⟩

omit [NumberField K] in

/- English proof (translation)
Establish `step : ∀ a : Fin (r + 1), (∀ x ∈ Λ, x ∈ F.Xa a.val → ∃ x' ∈ Λ, x' ∈ F'.Xa a.val ∧ x' - x ∈ smulLat g Λ) → ∀ (t : K) (x : V), x ∈ Λ → x - t • F.e a ∈ F.Xa a.val → ∃ x' ∈ Λ, x' - t • F'.e a ∈ F'.Xa a.val ∧ x' - x ∈ smulLat g Λ`. Introduce `a ih t x hx hxt`. Establish `ht : t ∈ lead F Λ a` using `by show t • F.e a ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val)`. Conclude with `Submodule.mem_sup.2 ⟨x, hx, -(x - t • F.e a), (F.Xa a.val).neg_mem hxt, by abel⟩`. Rewrite `ht` using `[hl]`.

Establish `ht' : t • F'.e a ∈ Λ ⊔ rs (𝓞 K) (F'.Xa a.val)` using `ht`. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 ht'`. Establish `hu' : u - t • F'.e a ∈ F'.Xa a.val`. Rewrite using `[← huv]`. Simplify using `using hv`.

Take `⟨x₁, hx₁, h1, h2⟩` from `h a t u hu hu'`. Establish `h3 : x - x₁ ∈ F.Xa a.val`. Use `(F.Xa a.val).sub_mem hxt h1` as an intermediate fact. Simplify using `using this`. Take `⟨x₂, hx₂, h4, h5⟩` from `ih _ (Λ.sub_mem hx hx₁) h3`.

Use `⟨u + x₂, Λ.add_mem hu hx₂, ?_, ?_⟩` and prove the remaining obligations. Use `(F'.Xa a.val).add_mem hu' h4` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Use `(smulLat g Λ).sub_mem h5 h2` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws. Establish `key : ∀ n : ℕ, n ≤ r → ∀ x ∈ Λ, x ∈ F.Xa n → ∃ x' ∈ Λ, x' ∈ F'.Xa n ∧ x' - x ∈ smulLat g Λ`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `_ x _ hx`. Rewrite `hx` using `[Xa_zero, Submodule.mem_bot]`. Substitute `hx` using the available equality. Conclude with `⟨0, Λ.zero_mem, Submodule.zero_mem _, by simp⟩`.

Consider the case `succ n ih`. Introduce `hn x hx hxn`. Set `a : Fin r` to `⟨n, hn⟩`. Take `⟨t, ht⟩` from `exists_coeff F a hxn`. Take `⟨x', hx', h1, h2⟩` from `step a.castSucc (ih (Nat.le_of_succ_le hn)) t x hx ht`.

Use `⟨x', hx', ?_, h2⟩` and prove the remaining obligations. Use `(F'.Xa (n + 1)).add_mem (Xa_le_succ F' n h1) ((F'.Xa (n + 1)).smul_mem t (e_mem_Xa F' a (Nat.lt_succ_self n)))` as an intermediate fact. Simplify using `using this`. Conclude with `fun a => step a (key a.val (Nat.le_of_lt_succ a.2))`.
-/
theorem isAdm_symm {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : 𝓞 K}
    (hl : ∀ a, lead F Λ a = lead F' Λ a) (h : IsAdm F F' Λ g) : IsAdm F' F Λ g := by
  have step : ∀ a : Fin (r + 1),
      (∀ x ∈ Λ, x ∈ F.Xa a.val → ∃ x' ∈ Λ, x' ∈ F'.Xa a.val ∧ x' - x ∈ smulLat g Λ) →
      ∀ (t : K) (x : V), x ∈ Λ → x - t • F.e a ∈ F.Xa a.val →
        ∃ x' ∈ Λ, x' - t • F'.e a ∈ F'.Xa a.val ∧ x' - x ∈ smulLat g Λ := by
    intro a ih t x hx hxt
    have ht : t ∈ lead F Λ a := by
      show t • F.e a ∈ Λ ⊔ rs (𝓞 K) (F.Xa a.val)
      exact Submodule.mem_sup.2 ⟨x, hx, -(x - t • F.e a), (F.Xa a.val).neg_mem hxt, by abel⟩
    rw [hl] at ht
    have ht' : t • F'.e a ∈ Λ ⊔ rs (𝓞 K) (F'.Xa a.val) := ht
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 ht'
    have hu' : u - t • F'.e a ∈ F'.Xa a.val := by
      rw [← huv]; simpa using hv
    obtain ⟨x₁, hx₁, h1, h2⟩ := h a t u hu hu'
    have h3 : x - x₁ ∈ F.Xa a.val := by
      have := (F.Xa a.val).sub_mem hxt h1
      simpa using this
    obtain ⟨x₂, hx₂, h4, h5⟩ := ih _ (Λ.sub_mem hx hx₁) h3
    refine ⟨u + x₂, Λ.add_mem hu hx₂, ?_, ?_⟩
    · have := (F'.Xa a.val).add_mem hu' h4
      convert this using 1; abel
    · have := (smulLat g Λ).sub_mem h5 h2
      convert this using 1; abel
  have key : ∀ n : ℕ, n ≤ r →
      ∀ x ∈ Λ, x ∈ F.Xa n → ∃ x' ∈ Λ, x' ∈ F'.Xa n ∧ x' - x ∈ smulLat g Λ := by
    intro n
    induction n with
    | zero =>
      intro _ x _ hx
      rw [Xa_zero, Submodule.mem_bot] at hx
      subst hx
      exact ⟨0, Λ.zero_mem, Submodule.zero_mem _, by simp⟩
    | succ n ih =>
      intro hn x hx hxn
      let a : Fin r := ⟨n, hn⟩
      obtain ⟨t, ht⟩ := exists_coeff F a hxn
      obtain ⟨x', hx', h1, h2⟩ := step a.castSucc (ih (Nat.le_of_succ_le hn)) t x hx ht
      refine ⟨x', hx', ?_, h2⟩
      have := (F'.Xa (n + 1)).add_mem (Xa_le_succ F' n h1)
        ((F'.Xa (n + 1)).smul_mem t (e_mem_Xa F' a (Nat.lt_succ_self n)))
      simpa using this
  exact fun a => step a (key a.val (Nat.le_of_lt_succ a.2))

/- English proof (translation)
Establish `hg0 : (g : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Rewrite `hy` using `[mem_iota]`. Take `⟨-, h2, l', hl', m, hm, h3, h4⟩` from `hy`. Take `⟨x, -, hx, hxg⟩` from `h (Fin.last r) 0 l' hl' (by simpa [FlagD.X] using h3)`. Take `⟨n, hn, hxn⟩` from `(mem_smulLat g Λ _).1 hxg`.

Establish `hx' : x ∈ F.X` using `by simpa [FlagD.X] using hx`. Rewrite using `[mem_smulLat]`. Use `⟨(g : K)⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hg0, one_smul]⟩` and prove the remaining obligations. Rewrite `h2`, the goal using `[mem_perp_lattice_flag_iff]`. Use `⟨fun v hv => by simp [h2.1 v hv], m - n, Λ.sub_mem hm hn, ?_⟩` and prove the remaining obligations.

Rewrite using `[← F.X.smul_mem_iff hg0, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul, smul_sub, ← hxn]`. Use `F.X.add_mem h4 hx'` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.
-/
theorem iota_ker {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (h : IsAdm F F' Λ (g : 𝓞 K)) {y : V} (hy : ((0 : V), y) ∈ iotaGraph F F' Λ (g : 𝓞 K)) :
    y ∈ smulLat (g : 𝓞 K) (flagPairDefinitePartLattice F F' Λ) := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [mem_iota] at hy
  obtain ⟨-, h2, l', hl', m, hm, h3, h4⟩ := hy
  obtain ⟨x, -, hx, hxg⟩ := h (Fin.last r) 0 l' hl' (by simpa [FlagD.X] using h3)
  obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 hxg
  have hx' : x ∈ F.X := by simpa [FlagD.X] using hx
  rw [mem_smulLat]
  refine ⟨(g : K)⁻¹ • y, ?_, by rw [smul_smul, mul_inv_cancel₀ hg0, one_smul]⟩
  rw [mem_perp_lattice_flag_iff] at h2 ⊢
  refine ⟨fun v hv => by simp [h2.1 v hv], m - n, Λ.sub_mem hm hn, ?_⟩
  rw [← F.X.smul_mem_iff hg0, smul_sub, smul_smul, mul_inv_cancel₀ hg0, one_smul, smul_sub, ← hxn]
  have := F.X.add_mem h4 hx'
  convert this using 1; abel

omit [NumberField K] in
/- English proof (translation)
Rewrite `hx` using `[← hU.2, mem_dual_iff]`. Conclude with `Submodule.mem_one.1 (hx.2 y hy)`.
-/
theorem integral_of_unimod {Λ : Submodule (𝓞 K) V} (hU : IsUnimod H Λ) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    ∃ t : 𝓞 K, (t : K) = H.B x y := by
  rw [← hU.2, mem_dual_iff] at hx
  exact Submodule.mem_one.1 (hx.2 y hy)

omit [NumberField K] in
/- English proof (translation)
Establish `a` using `h₁ _ (isotropicSpan_le_jointSpan_left F F' k₂)`. Establish `b` using `orth_symm (h₂ _ (isotropicSpan_le_jointSpan_left F F' k₁))`. Establish `c` using `X_iso F k₁ k₂`. Simplify using `only [map_sub, LinearMap.sub_apply] at a b c`. Take the linear combination `a + b - c`.
-/
theorem form_lift (F F' : FlagD H r) {y₁ y₂ l₁ l₂ : V} (h₁ : ∀ v ∈ V0 F F', H.B y₁ v = 0)
    (h₂ : ∀ v ∈ V0 F F', H.B y₂ v = 0) (k₁ : y₁ - l₁ ∈ F.X) (k₂ : y₂ - l₂ ∈ F.X) : H.B y₁ y₂ = H.B l₁ l₂ := by
  have a := h₁ _ (isotropicSpan_le_jointSpan_left F F' k₂)
  have b := orth_symm (h₂ _ (isotropicSpan_le_jointSpan_left F F' k₁))
  have c := X_iso F k₁ k₂
  simp only [map_sub, LinearMap.sub_apply] at a b c
  linear_combination a + b - c

omit [NumberField K] in

/- English proof (translation)
Take `⟨p1, p2, l, hl, m, hm, p3, p4⟩` from `(mem_iota F F' Λ g p.1 p.2).1 hp`. Take `⟨q1, q2, k, hk, n, hn, q3, q4⟩` from `(mem_iota F F' Λ g q.1 q.2).1 hq`. Rewrite `p1`, `p2`, `q1`, `q2` using `[mem_perp_lattice_flag_iff]`. Rewrite using `[form_lift F' F p1.1 q1.1 p3 q3, form_lift F F' p2.1 q2.1 p4 q4]`. Take `⟨a, ha⟩` from `integral_of_unimod hU hl hn`.

Take `⟨b, hb⟩` from `integral_of_unimod hU hm (Λ.add_mem hk (gsmul_mem g hn))`. Use `⟨-a - b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_natCast, map_sub, map_neg]`. Express the relevant statement in the definitionally equal form `_ = (g : K) * (-(a : K) - (b : K))`. Rewrite using `[ha, hb]`.

Simplify using `only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iota_form {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hU : IsUnimod H Λ) {p q : V × V}
    (hp : p ∈ iotaGraph F F' Λ (g : 𝓞 K)) (hq : q ∈ iotaGraph F F' Λ (g : 𝓞 K)) :
    ∃ t : 𝓞 K, H.B p.1 q.1 - H.B p.2 q.2 = algebraMap (𝓞 K) K ((g : 𝓞 K) * t) := by
  obtain ⟨p1, p2, l, hl, m, hm, p3, p4⟩ := (mem_iota F F' Λ g p.1 p.2).1 hp
  obtain ⟨q1, q2, k, hk, n, hn, q3, q4⟩ := (mem_iota F F' Λ g q.1 q.2).1 hq
  rw [mem_perp_lattice_flag_iff] at p1 p2 q1 q2
  rw [form_lift F' F p1.1 q1.1 p3 q3, form_lift F F' p2.1 q2.1 p4 q4]
  obtain ⟨a, ha⟩ := integral_of_unimod hU hl hn
  obtain ⟨b, hb⟩ := integral_of_unimod hU hm (Λ.add_mem hk (gsmul_mem g hn))
  refine ⟨-a - b, ?_⟩
  rw [map_mul, map_natCast, map_sub, map_neg]
  change _ = (g : K) * (-(a : K) - (b : K))
  rw [ha, hb]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
    smul_eq_mul]
  ring

/- English proof (translation)
Establish `hg0 : (g : K) ≠ 0` using `Nat.cast_ne_zero.2 (by omega)`. Take `⟨hperp, l', hl', hx'⟩` from `(mem_perp_lattice_flag_iff F' F Λ y').1 hy'`. Set `S : Submodule K V` to `F.X ⊔ Submodule.span K {F.z}`. Establish `hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) S), IsIntegral ℤ ((g : K)⁻¹ * H.B x l')`. Introduce and unpack `⟨x, hxΛ, hxS⟩`.

Take `⟨u, hu, v, hv, rfl⟩` from `Submodule.mem_sup.1 hxS`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hv`. Take `⟨x', -, h1, h2⟩` from `h (Fin.last r) t _ hxΛ (by show u + t • F.z - t • F.z ∈ F.X`. Simplify using `using hu)`. Take `⟨n, hn, hxn⟩` from `(mem_smulLat g Λ _).1 h2`.

Establish `h1' : x' - t • F'.z ∈ F'.X` using `h1`. Establish `a1` using `orth_symm (hperp _ (isotropicSpan_le_jointSpan_left F' F h1'))`. Establish `a2` using `orth_symm (hperp _ (lastVector_mem_jointSpan_left F' F))`. Establish `a3` using `X_iso F' h1' hx'`. Establish `a4` using `orth_symm (pairing_isotropicSpan_lastVector F' hx')`.

Establish `a5 : H.B (x' - (u + t • F.z)) l' = g * H.B n l'` using `by rw [hxn]; simp`. Take `⟨c, hc⟩` from `integral_of_unimod hU hn hl'`. Establish `: (g : K)⁻¹ * H.B (u + t • F.z) l' = ((-c : 𝓞 K) : K)`. Rewrite using `[inv_mul_eq_iff_eq_mul₀ hg0]`. Express the relevant statement in the definitionally equal form `_ = (g : K) * (-(c : K))`.

Rewrite using `[hc]`. Simplify using `only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at a1 a3 a4 a5`. Take the linear combination `a1 - a3 - a5 + t * a2 - t * a4`. Use `show IsIntegral ℤ ((g : K)⁻¹ * H.B (u + t • F.z) l')`. Rewrite using `[this]`.

Conclude with `(-c).isIntegral_coe`. Set `φ : ↥(Λ ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K` to `{ toFun := fun x => ⟨(g : K)⁻¹ * H.B x l', hdiv x⟩ map_add' := fun a b => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show (g : K)⁻¹ * H.B ((a : V) + b) l' = (g : K)⁻¹ * H.B a l' + (g : K)⁻¹ * H.B b l'`. Simplify using `[mul_add]`.

Use the proof step `map_smul' := fun a b => by`. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show (g : K)⁻¹ * H.B (a • (b : V)) l' = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l')`. Rewrite using `[← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]`. Use `ring }`.

Take `⟨m, hm, hφ⟩` from `GlobalTheory.UnimodQuot.exists_lattice_rep H hU S φ`. Establish `hw : ∀ a : Fin (r + 1), H.B (F.e a) (l' + (g : K) • (-m)) = 0`. Introduce `a`. Establish `haS : F.e a ∈ S`. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations.

Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)`. Conclude with `Submodule.mem_sup_left (e_mem_Xa F b b.2)`. Take `⟨s, hs⟩` from `GlobalTheory.UnimodQuot.exists_smul_mem ((isLatMod_top_bot_iff Λ).1 hU.1) (F.e a)`. Establish `hs0 : algebraMap (𝓞 K) K s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`. Establish `hs' : algebraMap (𝓞 K) K s • F.e a ∈ Λ` using `by rw [algebraMap_smul]; exact hs`.

Establish `e : H.B (algebraMap (𝓞 K) K s • F.e a) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • F.e a) l'` using `hφ ⟨_, hs', S.smul_mem _ haS⟩`. Rewrite `e` using `[eq_inv_mul_iff_mul_eq₀ hg0]`. Apply `mul_left_cancel₀ hs0` to reduce the goal to its premises. Simplify using `only [map_add, map_neg, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast, smul_eq_mul] at e ⊢`. Take the linear combination `-e`.

Take `⟨x, hx, hxw⟩` from `hlift _ hw`. Establish `hneg : l' + (g : K) • (-m) - x - (l' + (g : K) • (-m)) ∈ F.X`. Use `F.X.neg_mem hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Normalize the expressions using the abelian group laws.

Use `⟨l' + (g : K) • (-m) - x, (mem_iota F F' Λ g _ _).2 ⟨hy', ?_, l', hl', -m, Λ.neg_mem hm, hx', hneg⟩⟩` and prove the remaining obligations. Conclude with `(mem_perp_lattice_flag_iff F F' Λ _).2 ⟨fun v hv => orth_symm (hxw v hv), _, Λ.add_mem hl' (gsmul_mem g (Λ.neg_mem hm)), hneg⟩`.
-/
theorem iota_total [FiniteDimensional K V] {F F' : FlagD H r} {Λ : Submodule (𝓞 K) V} {g : ℕ} (hg : 1 ≤ g)
    (hU : IsUnimod H Λ) (h : IsAdm F' F Λ (g : 𝓞 K))
    (hlift : ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0)
    {y' : V} (hy' : y' ∈ flagPairDefinitePartLattice F' F Λ) : ∃ y, (y', y) ∈ iotaGraph F F' Λ (g : 𝓞 K) := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨hperp, l', hl', hx'⟩ := (mem_perp_lattice_flag_iff F' F Λ y').1 hy'
  let S : Submodule K V := F.X ⊔ Submodule.span K {F.z}
  have hdiv : ∀ x : ↥(Λ ⊓ rs (𝓞 K) S), IsIntegral ℤ ((g : K)⁻¹ * H.B x l') := by
    rintro ⟨x, hxΛ, hxS⟩
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hxS
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hv
    obtain ⟨x', -, h1, h2⟩ := h (Fin.last r) t _ hxΛ (by
      show u + t • F.z - t • F.z ∈ F.X
      simpa using hu)
    obtain ⟨n, hn, hxn⟩ := (mem_smulLat g Λ _).1 h2
    have h1' : x' - t • F'.z ∈ F'.X := h1
    have a1 := orth_symm (hperp _ (isotropicSpan_le_jointSpan_left F' F h1'))
    have a2 := orth_symm (hperp _ (lastVector_mem_jointSpan_left F' F))
    have a3 := X_iso F' h1' hx'
    have a4 := orth_symm (pairing_isotropicSpan_lastVector F' hx')
    have a5 : H.B (x' - (u + t • F.z)) l' = g * H.B n l' := by rw [hxn]; simp
    obtain ⟨c, hc⟩ := integral_of_unimod hU hn hl'
    have : (g : K)⁻¹ * H.B (u + t • F.z) l' = ((-c : 𝓞 K) : K) := by
      rw [inv_mul_eq_iff_eq_mul₀ hg0]
      change _ = (g : K) * (-(c : K))
      rw [hc]
      simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at a1 a3 a4 a5
      linear_combination a1 - a3 - a5 + t * a2 - t * a4
    show IsIntegral ℤ ((g : K)⁻¹ * H.B (u + t • F.z) l')
    rw [this]
    exact (-c).isIntegral_coe
  let φ : ↥(Λ ⊓ rs (𝓞 K) S) →ₗ[𝓞 K] 𝓞 K :=
    { toFun := fun x => ⟨(g : K)⁻¹ * H.B x l', hdiv x⟩
      map_add' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B ((a : V) + b) l' = (g : K)⁻¹ * H.B a l' + (g : K)⁻¹ * H.B b l'
        simp [mul_add]
      map_smul' := fun a b => by
        apply RingOfIntegers.ext
        show (g : K)⁻¹ * H.B (a • (b : V)) l' = algebraMap (𝓞 K) K a * ((g : K)⁻¹ * H.B b l')
        rw [← algebraMap_smul K a, map_smul, LinearMap.smul_apply, smul_eq_mul]
        ring }
  obtain ⟨m, hm, hφ⟩ := GlobalTheory.UnimodQuot.exists_lattice_rep H hU S φ
  have hw : ∀ a : Fin (r + 1), H.B (F.e a) (l' + (g : K) • (-m)) = 0 := by
    intro a
    have haS : F.e a ∈ S := by
      refine Fin.lastCases ?_ (fun b => ?_) a
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      · exact Submodule.mem_sup_left (e_mem_Xa F b b.2)
    obtain ⟨s, hs⟩ := GlobalTheory.UnimodQuot.exists_smul_mem ((isLatMod_top_bot_iff Λ).1 hU.1) (F.e a)
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    have hs' : algebraMap (𝓞 K) K s • F.e a ∈ Λ := by rw [algebraMap_smul]; exact hs
    have e : H.B (algebraMap (𝓞 K) K s • F.e a) m = (g : K)⁻¹ * H.B (algebraMap (𝓞 K) K s • F.e a) l' :=
      hφ ⟨_, hs', S.smul_mem _ haS⟩
    rw [eq_inv_mul_iff_mul_eq₀ hg0] at e
    apply mul_left_cancel₀ hs0
    simp only [map_add, map_neg, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, map_natCast,
      smul_eq_mul] at e ⊢
    linear_combination -e
  obtain ⟨x, hx, hxw⟩ := hlift _ hw
  have hneg : l' + (g : K) • (-m) - x - (l' + (g : K) • (-m)) ∈ F.X := by
    have := F.X.neg_mem hx
    convert this using 1; abel
  refine ⟨l' + (g : K) • (-m) - x, (mem_iota F F' Λ g _ _).2 ⟨hy', ?_, l', hl', -m, Λ.neg_mem hm, hx', hneg⟩⟩
  exact (mem_perp_lattice_flag_iff F F' Λ _).2 ⟨fun v hv => orth_symm (hxw v hv), _,
    Λ.add_mem hl' (gsmul_mem g (Λ.neg_mem hm)), hneg⟩

omit [NumberField K] in
/- English proof (translation)
Introduce and unpack `⟨y', y⟩ ⟨h', h⟩`. Take `⟨w', hw', rfl⟩` from `(mem_smulLat g _ y').1 h'`. Take `⟨w, hw, rfl⟩` from `(mem_smulLat g _ y).1 h`. Take `⟨-, l', hl', k'⟩` from `(mem_perp_lattice_flag_iff _ _ _ _).1 hw'`. Take `⟨-, l, hl, k⟩` from `(mem_perp_lattice_flag_iff _ _ _ _).1 hw`.

Use `(mem_iota F F' Λ g _ _).2 ⟨gsmul_mem g hw', gsmul_mem g hw, _, gsmul_mem g hl', l - l', Λ.sub_mem hl hl', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_sub]`. Conclude with `F'.X.smul_mem _ k'`. Use `F.X.smul_mem (g : K) k` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Simplify using `[smul_sub]`.
-/
theorem smul_prod_le (F F' : FlagD H r) (Λ : Submodule (𝓞 K) V) (g : ℕ) :
    (smulLat (g : 𝓞 K) (flagPairDefinitePartLattice F' F Λ)).prod (smulLat (g : 𝓞 K) (flagPairDefinitePartLattice F F' Λ)) ≤ iotaGraph F F' Λ (g : 𝓞 K) := by
  rintro ⟨y', y⟩ ⟨h', h⟩
  obtain ⟨w', hw', rfl⟩ := (mem_smulLat g _ y').1 h'
  obtain ⟨w, hw, rfl⟩ := (mem_smulLat g _ y).1 h
  obtain ⟨-, l', hl', k'⟩ := (mem_perp_lattice_flag_iff _ _ _ _).1 hw'
  obtain ⟨-, l, hl, k⟩ := (mem_perp_lattice_flag_iff _ _ _ _).1 hw
  refine (mem_iota F F' Λ g _ _).2 ⟨gsmul_mem g hw', gsmul_mem g hw, _, gsmul_mem g hl', l - l',
    Λ.sub_mem hl hl', ?_, ?_⟩
  · rw [← smul_sub]; exact F'.X.smul_mem _ k'
  · have := F.X.smul_mem (g : K) k
    convert this using 1
    simp [smul_sub]

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg ⟨⟨hU, hF, hF'⟩, hA⟩`. Take `⟨-, -, -, -, -, -, -, hl, hl'⟩` from `(GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1`. Establish `hA' : IsAdm N.F' N.F Λ (g : 𝓞 K)`. Use `isAdm_symm (fun a => ?_) hA` and prove the remaining obligations. Use `Fin.lastCases ?_ (fun b => ?_) a` and prove the remaining obligations.

Rewrite using `[hF.2, hF'.2]`. Rewrite using `[hF.1, hF'.1]`. Use `⟨inf_le_left, smul_prod_le _ _ _ _, fun y' hy' => iota_total hg hU hA' hl hy', fun y hy => ?_, fun y hy => iota_ker hg hA hy, fun y hy => iota_ker hg hA' (iota_swap hy), fun p hp q hq => iota_form hU hp hq⟩` and prove the remaining obligations. Take `⟨y', h⟩` from `iota_total hg hU hA (by rw [jointSpan_comm]; exact hl') hy`. Conclude with `⟨y', iota_swap h⟩`.
-/
theorem isModIso_iota : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → IsModIso H (g : 𝓞 K) (flagPairDefinitePartLattice N.F' N.F Λ) (flagPairDefinitePartLattice N.F N.F' Λ) (iotaGraph N.F N.F' Λ (g : 𝓞 K)) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg ⟨⟨hU, hF, hF'⟩, hA⟩
  obtain ⟨-, -, -, -, -, -, -, hl, hl'⟩ := (GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N).1
  have hA' : IsAdm N.F' N.F Λ (g : 𝓞 K) := by
    refine isAdm_symm (fun a => ?_) hA
    refine Fin.lastCases ?_ (fun b => ?_) a
    · rw [hF.2, hF'.2]
    · rw [hF.1, hF'.1]
  refine ⟨inf_le_left, smul_prod_le _ _ _ _, fun y' hy' => iota_total hg hU hA' hl hy', fun y hy => ?_,
    fun y hy => iota_ker hg hA hy, fun y hy => iota_ker hg hA' (iota_swap hy), fun p hp q hq => iota_form hU hp hq⟩
  obtain ⟨y', h⟩ := iota_total hg hU hA (by rw [jointSpan_comm]; exact hl') hy
  exact ⟨y', iota_swap h⟩

end GlobalTheory.ModIdent
