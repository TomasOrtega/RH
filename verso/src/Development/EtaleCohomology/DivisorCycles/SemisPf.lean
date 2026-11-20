import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.SemisPf
open LateralTheory.DivDb

variable {C : Type} [Field C] {N : ℕ}

def img {A : Subalgebra C (Mat C N)} (I : Ideal A) : Submodule C (Fin N → C) :=
  Submodule.span C {w | ∃ x ∈ I, ∃ v, w = (x : Mat C N) *ᵥ v}

/- English proof (translation)
Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨y, hy, v, rfl⟩` from `hw`. Use `Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩` and prove the remaining obligations. Simplify using `[Matrix.mulVec_mulVec]`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ c ha`.
-/
lemma img_step {A : Subalgebra C (Mat C N)} (J I : Ideal A) {x : A} (hx : x ∈ J) {u : Fin N → C}
    (hu : u ∈ img I) : (x : Mat C N) *ᵥ u ∈ img (J * I) := by
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨y, hy, v, rfl⟩ := hw
    refine Submodule.subset_span ⟨x * y, Submodule.mul_mem_mul hx hy, v, ?_⟩
    simp [Matrix.mulVec_mulVec]
  | zero => simp
  | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
  | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha

/- English proof (translation)
Rewrite using `[img, Submodule.span_eq_bot]`. Introduce and unpack `w ⟨x, hx, v, rfl⟩`. Rewrite `hx` using `[Submodule.mem_bot]`. Simplify using `[hx]`.
-/
lemma img_bot {A : Subalgebra C (Mat C N)} : img (⊥ : Ideal A) = ⊥ := by
  rw [img, Submodule.span_eq_bot]
  rintro w ⟨x, hx, v, rfl⟩
  rw [Submodule.mem_bot] at hx
  simp [hx]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[pow_succ, ih, pow_succ B (n+1)]`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma conj_pow (P B Q : Mat C N) (h : Q * P = 1) (n : ℕ) : (P * B * Q) ^ (n + 1) = P * B ^ (n + 1) * Q := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, pow_succ B (n+1)]
    calc P * B ^ (n + 1) * Q * (P * B * Q) = P * B ^ (n + 1) * (Q * P) * B * Q := by noncomm_ring
      _ = _ := by rw [h]; noncomm_ring

/- English proof (translation)
Take `⟨k, hk⟩` from `hB`. Use `⟨k + 1, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_pow P B Q h, pow_succ, hk]`. Simplify using the standard rewrite rules.
-/
lemma nil_conj (P B Q : Mat C N) (h : Q * P = 1) (hB : IsNilpotent B) : IsNilpotent (P * B * Q) := by
  obtain ⟨k, hk⟩ := hB
  refine ⟨k + 1, ?_⟩
  rw [conj_pow P B Q h, pow_succ, hk]; simp

/- English proof (translation)
Rewrite using `[← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]`.
-/
lemma inv_mul_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g⁻¹ : Mat C N) * (ρ g : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]

/- English proof (translation)
Rewrite using `[← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]`.
-/
lemma mul_inv_rho {Γ : Type} [Group Γ] (ρ : Γ →* GL (Fin N) C) (g : Γ) :
    (ρ g : Mat C N) * (ρ g⁻¹ : Mat C N) = 1 := by
  rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]

/- English proof (translation)
Introduce `Γ C _ _ N ρ A hss hn hk Y hYA hY`. Set `S : Set (Mat C N)` to `{Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}`. Set `U : Submodule C (Fin N → C)` to `Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}`. Establish `hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U`. Introduce `g v hv`.

Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem w hw`. Take `⟨Z, ⟨hZA, hZ⟩, v, rfl⟩` from `hw`. Use `Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩, (ρ g : Mat C N) *ᵥ v, ?_⟩` and prove the remaining obligations. Introduce `a ha`.

Establish `ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A` using `hn g⁻¹ a ha`. Rewrite `ha'` using `[inv_inv]`. Use `nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z) (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_inv_rho]`. Simplify using the standard rewrite rules. Use `_ = _ := by noncomm_ring`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]`. Consider the case `zero => simp`.

Consider the case `add a b _ _ ha hb => rw [Matrix.mulVec_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ c ha`. Take `⟨W, hcompl, hWst⟩` from `hss U hUst`.

Establish `hWA` using `hk W hWst`. Establish `hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0`. Introduce `Z hZ w hw`. Establish `h1 : Z *ᵥ w ∈ U` using `Submodule.subset_span ⟨Z, hZ, w, rfl⟩`. Establish `h2 : Z *ᵥ w ∈ W` using `hWA Z hZ.1 w hw`.

Use `hcompl.inf_eq_bot` as an intermediate fact. Establish `h3 : Z *ᵥ w ∈ U ⊓ W` using `⟨h1, h2⟩`. Rewrite `h3` using `[this]`. Conclude with `(Submodule.mem_bot C).1 h3`. Establish `: IsArtinianRing A` using `IsArtinianRing.of_finite C A`.

Set `J : Ideal A` to `Ideal.jacobson ⊥`. Establish `hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J`. Introduce `Z hZ`. Rewrite using `[Ideal.mem_jacobson_iff]`. Introduce `y`.

Establish `hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A))`. Take `⟨k, hk'⟩` from `hZ.2 y y.2`. Use `⟨k, Subtype.ext ?_⟩` and prove the remaining obligations. Simplify using `using hk'`. Establish `hu` using `hnil.isUnit_one_add`.

Use `⟨↑hu.unit⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.mem_bot]`. Establish `h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1` using `hu.val_inv_mul`. Combine the equalities or inequalities in the displayed calculation. Take `⟨m, hm⟩` from `IsArtinianRing.isNilpotent_jacobson_bot (R := A)`.

Establish `key : ∀ k : ℕ, U ≤ img (J ^ (k + 1))`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[Submodule.pow_one]`.

Use `show Submodule.span C _ ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨Z, hZ, v, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩`. Consider the case `succ k ih => show Submodule.span C _ ≤ _`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `w ⟨Z, hZ, v, rfl⟩`. Establish `hv : v ∈ U ⊔ W` using `hcompl.sup_eq_top ▸ Submodule.mem_top`. Take `⟨u, hu, w', hw', rfl⟩` from `Submodule.mem_sup.1 hv`. Use `show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))`.

Rewrite using `[Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]`. Conclude with `img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)`. Establish `hU : U = ⊥`. Establish `h` using `key m`. Establish `hb : J ^ (m + 1) = ⊥`.

Rewrite using `[Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]`. Rewrite `h` using `[hb, img_bot]`. Conclude with `le_bot_iff.1 h`. Use extensionality with `i j`. Establish `hv : Y *ᵥ Pi.single j 1 ∈ U` using `Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩`.

Rewrite `hv` using `[hU, Submodule.mem_bot]`. Simplify using `using congrFun hv i`.
-/
theorem Semis_of : Semis := by
  intro Γ C _ _ N ρ A hss hn hk Y hYA hY

  let S : Set (Mat C N) := {Z | Z ∈ A ∧ ∀ a ∈ A, IsNilpotent (a * Z)}
  let U : Submodule C (Fin N → C) := Submodule.span C {w | ∃ Z ∈ S, ∃ v, w = Z *ᵥ v}
  have hUst : ∀ g, ∀ v ∈ U, (ρ g : Mat C N) *ᵥ v ∈ U := by
    intro g v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨Z, ⟨hZA, hZ⟩, v, rfl⟩ := hw
      refine Submodule.subset_span ⟨(ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N), ⟨hn g Z hZA, ?_⟩,
        (ρ g : Mat C N) *ᵥ v, ?_⟩
      · intro a ha
        have ha' : (ρ g⁻¹ : Mat C N) * a * (ρ g⁻¹⁻¹ : Mat C N) ∈ A := hn g⁻¹ a ha
        rw [inv_inv] at ha'
        have := nil_conj (ρ g : Mat C N) ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N) * Z)
          (ρ g⁻¹ : Mat C N) (inv_mul_rho ρ g) (hZ ((ρ g⁻¹ : Mat C N) * a * (ρ g : Mat C N)) ha')
        convert this using 1
        calc a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N))
            = ((ρ g : Mat C N) * (ρ g⁻¹ : Mat C N)) * a * ((ρ g : Mat C N) * Z * (ρ g⁻¹ : Mat C N)) := by
              rw [mul_inv_rho]; simp
          _ = _ := by noncomm_ring
      · rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc ((ρ g : Mat C N) * Z), inv_mul_rho, mul_one]
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact add_mem ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨W, hcompl, hWst⟩ := hss U hUst
  have hWA := hk W hWst
  have hkill : ∀ Z ∈ S, ∀ w ∈ W, Z *ᵥ w = 0 := by
    intro Z hZ w hw
    have h1 : Z *ᵥ w ∈ U := Submodule.subset_span ⟨Z, hZ, w, rfl⟩
    have h2 : Z *ᵥ w ∈ W := hWA Z hZ.1 w hw
    have := hcompl.inf_eq_bot
    have h3 : Z *ᵥ w ∈ U ⊓ W := ⟨h1, h2⟩
    rw [this] at h3
    exact (Submodule.mem_bot C).1 h3
  have : IsArtinianRing A := IsArtinianRing.of_finite C A
  let J : Ideal A := Ideal.jacobson ⊥
  have hSJ : ∀ Z (hZ : Z ∈ S), (⟨Z, hZ.1⟩ : A) ∈ J := by
    intro Z hZ
    rw [Ideal.mem_jacobson_iff]
    intro y
    have hnil : IsNilpotent (y * (⟨Z, hZ.1⟩ : A)) := by
      obtain ⟨k, hk'⟩ := hZ.2 y y.2
      refine ⟨k, Subtype.ext ?_⟩
      simpa using hk'
    have hu := hnil.isUnit_one_add
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [Ideal.mem_bot]
    have h1 : (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) = 1 := hu.val_inv_mul
    calc (↑hu.unit⁻¹ : A) * y * (⟨Z, hZ.1⟩ : A) + ↑hu.unit⁻¹ - 1
        = (↑hu.unit⁻¹ : A) * (1 + y * (⟨Z, hZ.1⟩ : A)) - 1 := by noncomm_ring
      _ = 0 := by rw [h1, sub_self]
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  have key : ∀ k : ℕ, U ≤ img (J ^ (k + 1)) := by
    intro k
    induction k with
    | zero =>
      rw [Submodule.pow_one]
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      exact Submodule.subset_span ⟨⟨Z, hZ.1⟩, hSJ Z hZ, v, rfl⟩
    | succ k ih =>
      show Submodule.span C _ ≤ _
      rw [Submodule.span_le]
      rintro w ⟨Z, hZ, v, rfl⟩
      have hv : v ∈ U ⊔ W := hcompl.sup_eq_top ▸ Submodule.mem_top
      obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.1 hv
      show Z *ᵥ (u + w') ∈ img (J ^ (k + 1 + 1))
      rw [Matrix.mulVec_add, hkill Z hZ w' hw', add_zero, Ideal.IsTwoSided.pow_succ]
      exact img_step J _ (x := ⟨Z, hZ.1⟩) (hSJ Z hZ) (ih hu)
  have hU : U = ⊥ := by
    have h := key m
    have hb : J ^ (m + 1) = ⊥ := by
      rw [Submodule.pow_succ, hm, Submodule.zero_eq_bot, Submodule.bot_mul]
    rw [hb, img_bot] at h
    exact le_bot_iff.1 h
  ext i j
  have hv : Y *ᵥ Pi.single j 1 ∈ U := Submodule.subset_span ⟨Y, ⟨hYA, hY⟩, Pi.single j 1, rfl⟩
  rw [hU, Submodule.mem_bot] at hv
  simpa using congrFun hv i
end LateralTheory.DivDb.SemisPf
