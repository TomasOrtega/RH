import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.WeightChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdFlagU
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaExists
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.HeckeGal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Use `w.isMaximal` as an intermediate fact. Use `letI := Ideal.Quotient.field w.asIdeal`. Establish `: Finite (𝓞 F ⧸ w.asIdeal)` using `Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot`. Use `⟨Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩` and prove the remaining obligations. Use `letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)`.

Establish `hd : l ∣ normV w`. Rewrite using `[normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card]`. Rewrite `hw` using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec]`. Establish `hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime` using `CharP.prime_ringChar _`. Rewrite using `[(Nat.prime_dvd_prime_iff_eq hq Fact.out).1 hw]`.

Rewrite using `[← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']`. Conclude with `Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)` after adjusting the coercions.
-/
private theorem norm_q {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
    (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) : ((normV w : ℕ) : Qbar l) ≠ 0 ∧ ‖((normV w : ℕ) : Qbar l)‖ < 1 := by
  have := w.isMaximal
  letI := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 F ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  refine ⟨Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
  letI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd : l ∣ normV w := by
    rw [normV, Nat.card_eq_fintype_card, ← prime_dvd_char_iff_dvd_card]
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ringChar.spec] at hw
    have hq : (ringChar (𝓞 F ⧸ w.asIdeal)).Prime := CharP.prime_ringChar _
    rw [(Nat.prime_dvd_prime_iff_eq hq Fact.out).1 hw]
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact_mod_cast Padic.norm_intCast_lt_one_iff.2 (Int.natCast_dvd_natCast.2 hd)

/- English proof (translation)
Rewrite using `[GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV, Complex.cpow_intCast, mul_comm, zpow_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
private theorem abs_art {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}
    {a : Weil h →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (c : ℤ) (s : Weil h) :
    (GlobalTheory.SmGL.absPow (w.adicCompletion F) (c : ℂ) (a s) : ℂ) = ((normV w : ℕ) : ℂ) ^ (c * deg s) := by
  rw [GlobalTheory.SmGL.val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV, Complex.cpow_intCast,
    mul_comm, zpow_mul]
  push_cast
  rfl

/- English proof (translation)
Use `continuous_of_continuousAt_one f ?_` and prove the remaining obligations. Use `(continuousAt_const (y := (1 : B))).congr ?_` and prove the remaining obligations. Use `filter_upwards [hf.mem_nhds f.ker.one_mem] with x hx`. Conclude with `(MonoidHom.mem_ker.1 hx).symm`.
-/
private theorem cont_smooth {X : Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] {B : Type} [Group B]
    [TopologicalSpace B] [IsTopologicalGroup B] (f : X →* B) (hf : IsOpen (f.ker : Set X)) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  refine (continuousAt_const (y := (1 : B))).congr ?_
  filter_upwards [hf.mem_nhds f.ker.one_mem] with x hx
  exact (MonoidHom.mem_ker.1 hx).symm

/- English proof (translation)
Introduce `N F Ω _ _ _ _ _ l _ hl ι n w hw A h a ha r hr m hm ω hω hn hD`. Take `⟨q0, q1⟩` from `norm_q w hw`. Establish `q2 : 0 < ‖((normV w : ℕ) : Qbar l)‖` using `norm_pos_iff.2 q0`. Establish `hcyc : Continuous (cycBar F Ω l)` using `(Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)`. Establish `key : ∀ j, ∃ κ : Dec (F` using `F) A →* (Qbar l)ˣ, Continuous κ ∧ ∀ s : Weil h, (κ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) = ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by`.

Introduce `j`. Set `φ` to `ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ)`. Establish `hφ : GlobalTheory.SmGL.IsSmoothChar φ` using `(hω j).mul (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _))`. Set `ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ` to `(Units.map ι.symm.toRingHom.toMonoidHom).comp φ`. Establish `hξ : ∀ s, (ξ (a s) : Qbar l) = ι.symm (ω j (a s) : ℂ) * ((normV w : ℕ) : Qbar l) ^ (-m j * deg s)`.

Introduce `s`. Use `show ι.symm ((ω j (a s) : ℂ) * (GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ) (a s) : ℂ)) = _`. Rewrite using `[abs_art ha, map_mul, map_zpow₀, map_natCast]`. Establish `hc : Continuous ξ`. Use `cont_smooth ξ (Subgroup.isOpen_mono (fun x hx => ?_) hφ)` and prove the remaining obligations.

Rewrite `hx`, the goal using `[MonoidHom.mem_ker]`. Rewrite using `[MonoidHom.comp_apply, hx, map_one]`. Take `⟨κ, ⟨c1, c2⟩, -⟩` from `UpperTheory.V.Loc.laExists N.aut.art h a ha ξ hc fun x => by`. Take `⟨s, rfl⟩` from `ha.surj x`. Rewrite using `[hξ, norm_mul, hn, norm_zpow, ← zpow_add₀ q2.ne', neg_mul, add_neg_cancel, zpow_zero]`.

Use `⟨κ * ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m j, c1.mul ((continuous_zpow (m j)).comp (hcyc.comp continuous_subtype_val)), fun s => ?_⟩` and prove the remaining obligations. Use `show ((κ (Subgroup.inclusion (Weil_le_Dec h) s) * cycBar F Ω l (s : G F Ω) ^ m j : (Qbar l)ˣ) : Qbar l) * _ = _`. Rewrite using `[c2, Units.val_mul, hξ, Units.val_zpow_eq_zpow_val, neg_mul, zpow_neg, mul_right_comm, inv_mul_cancel_right₀ (zpow_ne_zero _ q0)]`. Use `choose κ hκ hv using key`. Use `⟨κ, (UpperTheory.V.Loc.ordFlagU N F Ω l hl ι n w hw A h a ha r hr (fun j _ => -m j) (fun _ i j hij => ?_) ω κ (fun j => ⟨hω j, hκ j, fun s g hg _ => ?_⟩) (fun i j hij => ?_) hD).1, hv⟩` and prove the remaining obligations.

Use `hm i j hij show -m i < -m j` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `rfl : g = Subgroup.inclusion (Weil_le_Dec h) s` from `Subtype.ext hg`. Establish `h1` using `hv j s`. Rewrite `h1` using `[UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s, mul_zpow, ← zpow_mul, mul_comm (deg s), mul_comm (_ ^ _), ← mul_assoc]`.

Use `(mul_right_cancel₀ (zpow_ne_zero _ q0) h1).trans ?_` and prove the remaining obligations. Use `congr 1`. Use `haveI := finite_contEmb (l := l) w`. Use `letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}`. Unfold `Hi.algPow`.

Rewrite using `[finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]`. Simplify using the standard rewrite rules. Establish `hi` using `hn i (frob h)`. Establish `hj` using `hn j (frob h)`. Rewrite `hi`, `hj` using `[deg_frob, mul_one]`.

Establish `hij' : m i ≠ m j ∧ m i ≠ m j + 1`. Break down `lt_or_gt_of_ne hij with h1 | h1` into its components or cases. Use `hm _ _ h1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `hm _ _ h1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `⟨fun e => hij'.1 ?_, fun e => hij'.2 ?_⟩` and prove the remaining obligations. Rewrite `hi` using `[e, hj]`. Conclude with `(zpow_right_injective₀ q2 q1.ne hi).symm`. Establish `h1` using `abs_art ha 1 (frob h)`.

Rewrite `h1` using `[deg_frob, mul_one, zpow_one, Int.cast_one]`. Rewrite `hi` using `[e, MonoidHom.mul_apply, Units.val_mul, h1, map_mul, map_natCast, norm_mul, hj, ← zpow_add_one₀ q2.ne']`. Conclude with `(zpow_right_injective₀ q2 q1.ne hi).symm`.
-/
theorem UpperTheory.deRham_weights_of_localArtin_characters :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (ι : Qbar l ≃+* ℂ) (n : ℕ) (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion F)ˣ), IsLocalArtin h a → ∀ (r : Dec (F := F) A →* GL (Fin n) (Qbar l)), Continuous r → ∀ (m : Fin n → ℤ), (∀ i j, i < j → m j + 2 ≤ m i) → ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ), (∀ j, GlobalTheory.SmGL.IsSmoothChar (ω j)) → (∀ j (s : Weil h), ‖ι.symm (ω j (a s) : ℂ)‖ = ‖((normV w : ℕ) : Qbar l)‖ ^ (m j * deg s)) → Hi.DRat ι h r (fun _ => Finset.univ.val.map fun j => -m j) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) → ∃ κ : Fin n → Dec (F := F) A →* (Qbar l)ˣ, W.HasFlag r κ ∧ ∀ j (s : Weil h), (κ j (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) = ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
  intro N F Ω _ _ _ _ _ l _ hl ι n w hw A h a ha r hr m hm ω hω hn hD
  obtain ⟨q0, q1⟩ := norm_q w hw
  have q2 : 0 < ‖((normV w : ℕ) : Qbar l)‖ := norm_pos_iff.2 q0
  have hcyc : Continuous (cycBar F Ω l) :=
    (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
      ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)
  have key : ∀ j, ∃ κ : Dec (F := F) A →* (Qbar l)ˣ, Continuous κ ∧ ∀ s : Weil h,
      (κ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) * ((normV w : ℕ) : Qbar l) ^ (m j * deg s) =
        ι.symm (ω j (a s) : ℂ) * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ m j := by
    intro j
    let φ := ω j * GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ)
    have hφ : GlobalTheory.SmGL.IsSmoothChar φ :=
      (hω j).mul (GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_absPow _ _))
    let ξ : (w.adicCompletion F)ˣ →* (Qbar l)ˣ := (Units.map ι.symm.toRingHom.toMonoidHom).comp φ
    have hξ : ∀ s, (ξ (a s) : Qbar l) = ι.symm (ω j (a s) : ℂ) * ((normV w : ℕ) : Qbar l) ^ (-m j * deg s) := by
      intro s
      show ι.symm ((ω j (a s) : ℂ) * (GlobalTheory.SmGL.absPow (w.adicCompletion F) ((-m j : ℤ) : ℂ) (a s) : ℂ)) = _
      rw [abs_art ha, map_mul, map_zpow₀, map_natCast]
    have hc : Continuous ξ := by
      refine cont_smooth ξ (Subgroup.isOpen_mono (fun x hx => ?_) hφ)
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]
    obtain ⟨κ, ⟨c1, c2⟩, -⟩ := UpperTheory.V.Loc.laExists N.aut.art h a ha ξ hc fun x => by
      obtain ⟨s, rfl⟩ := ha.surj x
      rw [hξ, norm_mul, hn, norm_zpow, ← zpow_add₀ q2.ne', neg_mul, add_neg_cancel, zpow_zero]
    refine ⟨κ * ((cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m j,
      c1.mul ((continuous_zpow (m j)).comp (hcyc.comp continuous_subtype_val)), fun s => ?_⟩
    show ((κ (Subgroup.inclusion (Weil_le_Dec h) s) * cycBar F Ω l (s : G F Ω) ^ m j : (Qbar l)ˣ) : Qbar l) * _ = _
    rw [c2, Units.val_mul, hξ, Units.val_zpow_eq_zpow_val, neg_mul, zpow_neg, mul_right_comm,
      inv_mul_cancel_right₀ (zpow_ne_zero _ q0)]
  choose κ hκ hv using key
  refine ⟨κ, (UpperTheory.V.Loc.ordFlagU N F Ω l hl ι n w hw A h a ha r hr (fun j _ => -m j)
    (fun _ i j hij => ?_) ω κ (fun j => ⟨hω j, hκ j, fun s g hg _ => ?_⟩) (fun i j hij => ?_) hD).1, hv⟩
  · have := hm i j hij
    show -m i < -m j
    omega
  · obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
    have h1 := hv j s
    rw [UpperTheory.V.Loc.epsArt N.aut.art h hw a ha s, mul_zpow, ← zpow_mul, mul_comm (deg s), mul_comm (_ ^ _),
      ← mul_assoc] at h1
    refine (mul_right_cancel₀ (zpow_ne_zero _ q0) h1).trans ?_
    congr 1
    haveI := finite_contEmb (l := l) w
    letI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
    unfold Hi.algPow
    rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
    simp
  · have hi := hn i (frob h)
    have hj := hn j (frob h)
    rw [deg_frob, mul_one] at hi hj
    have hij' : m i ≠ m j ∧ m i ≠ m j + 1 := by
      rcases lt_or_gt_of_ne hij with h1 | h1
      · have := hm _ _ h1; omega
      · have := hm _ _ h1; omega
    refine ⟨fun e => hij'.1 ?_, fun e => hij'.2 ?_⟩
    · rw [e, hj] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
    · have h1 := abs_art ha 1 (frob h)
      rw [deg_frob, mul_one, zpow_one, Int.cast_one] at h1
      rw [e, MonoidHom.mul_apply, Units.val_mul, h1, map_mul, map_natCast, norm_mul, hj, ← zpow_add_one₀ q2.ne'] at hi
      exact (zpow_right_injective₀ q2 q1.ne hi).symm
