import ReciprocityTheory.ClassFieldTheory.LocalClassField.KummerA
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

namespace Kummer

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n`. Conclude with `⟨_, hζ.isUnit_unit (NeZero.ne n)⟩`.
-/
theorem exists_primitive_unit : ∃ ζ : (PadicAlgCl p)ˣ, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) n
  exact ⟨_, hζ.isUnit_unit (NeZero.ne n)⟩

/- English proof (translation)
The claim follows from `(Continuous.isClosedEmbedding continuous_of_discreteTopology (muMap_injective hζ)).isEmbedding`.
-/
theorem isEmbedding_muMap {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) :
    Topology.IsEmbedding (muMap ζ hζ.pow_eq_one) :=
  (Continuous.isClosedEmbedding continuous_of_discreteTopology (muMap_injective hζ)).isEmbedding

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_primitive_unit p n`. Use `show Continuous fun q : GK p K × ZMod n => muRep p K n q.1 q.2`. Rewrite using `[(isEmbedding_muMap p n hζ).continuous_iff]`. Establish `h : (muMap ζ hζ.pow_eq_one ∘ fun q : GK p K × ZMod n => muRep p K n q.1 q.2) = fun q => kbarRep p K q.1 (muMap ζ hζ.pow_eq_one q.2)` using `funext fun q => muMap_equiv K ζ _ q.1 q.2`. Rewrite using `[h]`.

Conclude with `(contAction_kbarRep p K).comp (f := fun q : GK p K × ZMod n => (q.1, muMap ζ hζ.pow_eq_one q.2)) (continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd))`.
-/
theorem contAction_muRep : ReciprocityTheory.Gal.ContAction (muRep p K n) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  show Continuous fun q : GK p K × ZMod n => muRep p K n q.1 q.2
  rw [(isEmbedding_muMap p n hζ).continuous_iff]
  have h : (muMap ζ hζ.pow_eq_one ∘ fun q : GK p K × ZMod n => muRep p K n q.1 q.2) =
      fun q => kbarRep p K q.1 (muMap ζ hζ.pow_eq_one q.2) := funext fun q => muMap_equiv K ζ _ q.1 q.2
  rw [h]
  exact (contAction_kbarRep p K).comp (f := fun q : GK p K × ZMod n => (q.1, muMap ζ hζ.pow_eq_one q.2))
    (continuous_fst.prodMk (continuous_of_discreteTopology.comp continuous_snd))

def muT : TRep ℤ (GK p K) where
  V := ZMod n
  rho := muRep p K n
  cont := contAction_muRep p K n

variable {p n} in

def iP {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : Pair (muT p K n) (kT p K) :=
  Pair.ofMap (M := muT p K n) (M' := kT p K) (muMap ζ hζ.pow_eq_one)
    (continuous_of_discreteTopology : Continuous (muMap ζ hζ.pow_eq_one : ZMod n → KbarMult p))
    (muMap_equiv K ζ _)

def pP : Pair (kT p K) (kT p K) :=
  Pair.ofMap (M := kT p K) (M' := kT p K) (powMap p n)
    (continuous_of_discreteTopology : Continuous (powMap p n : KbarMult p → KbarMult p))
    fun g m => (map_zsmul (kbarRep p K g) (n : ℤ) m).symm

variable {p n} in
/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, rfl, isEmbedding_muMap p n hζ, exact_muMap_powMap hζ, ⟨Function.surjInv (powMap_surjective (p := p) (n := n)), (continuous_of_discreteTopology : Continuous (Function.surjInv (powMap_surjective (p := p) (n := n)))), Function.surjInv_eq _⟩⟩`.
-/
theorem adm {ζ : (PadicAlgCl p)ˣ} (hζ : IsPrimitiveRoot ζ n) : admitted (iP K hζ) (pP p K n) :=
  ⟨rfl, rfl, isEmbedding_muMap p n hζ, exact_muMap_powMap hζ,
    ⟨Function.surjInv (powMap_surjective (p := p) (n := n)),
      (continuous_of_discreteTopology : Continuous (Function.surjInv (powMap_surjective (p := p) (n := n)))),
      Function.surjInv_eq _⟩⟩

def unitsToInvariants' : Additive Kˣ →+ ReciprocityTheory.Gal.H0 (kT p K).rho where
  toFun a := ⟨(Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul) : KbarMult p),
    fun σ => Units.ext (σ.commutes _)⟩
  map_zero' := Subtype.ext (by simp; rfl)
  map_add' a b := Subtype.ext (by simp; rfl)

/- English proof (translation)
Introduce `a b hab`. Establish `h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul = Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul` using `congrArg Subtype.val hab`. Conclude with `Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1`.
-/
theorem units_to_invariants_prime_injective : Function.Injective (unitsToInvariants' p K) := by
  intro a b hab
  have h1 : Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) a.toMul =
      Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b.toMul := congrArg Subtype.val hab
  exact Units.map_injective (algebraMap K (PadicAlgCl p)).injective h1

/- English proof (translation)
Introduce and unpack `⟨x, hx⟩`. Establish `: IsGalois K (PadicAlgCl p)` using `isGalois_iff.mpr ⟨inferInstance, inferInstance⟩`. Establish `h1 : ∀ σ : GK p K, σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ)` using `fun σ => congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (hx σ)`. Take `⟨a, ha⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 h1`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Rewrite `ha` using `[map_zero]`. Conclude with `(Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero ha.symm`. Conclude with `⟨Additive.ofMul (Units.mk0 a ha0), Subtype.ext (Units.ext ha)⟩`.
-/
theorem units_to_invariants_prime_surjective : Function.Surjective (unitsToInvariants' p K) := by
  rintro ⟨x, hx⟩
  have : IsGalois K (PadicAlgCl p) := isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  have h1 : ∀ σ : GK p K, σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) = (Additive.toMul x : (PadicAlgCl p)ˣ) :=
    fun σ => congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) (hx σ)
  obtain ⟨a, ha⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact (Additive.toMul x : (PadicAlgCl p)ˣ).ne_zero ha.symm
  exact ⟨Additive.ofMul (Units.mk0 a ha0), Subtype.ext (Units.ext ha)⟩

/- English proof (translation)
Use `Subtype.ext ?_` and prove the remaining obligations. Use `show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _`. Rewrite using `[powMap_apply, ← map_pow]`. Both sides reduce to the same expression.
-/
theorem power_map_h0_unitsToInvariants (b : Kˣ) :
    (pP p K n).h0 (unitsToInvariants' p K (Additive.ofMul b)) = unitsToInvariants' p K (Additive.ofMul (b ^ n)) := by
  refine Subtype.ext ?_
  show powMap p n (Additive.ofMul (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p) b) : KbarMult p) = _
  rw [powMap_apply, ← map_pow]
  rfl

end

end Kummer

open Kummer

/- English proof (translation)
Take `⟨ζ, hζ⟩` from `exists_primitive_unit p n`. Take `⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩` from `low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)`. Establish `h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho)` using `h90`. Establish `hs : Function.Surjective δ₀` using `fun y => (e3 y).1 (Subsingleton.elim _ _)`. Set `ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho)` to `AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))`.

Establish `hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a)))` using `fun a => rfl`. Establish `hψs : Function.Surjective ψ`. Introduce `y`. Take `⟨x, hx⟩` from `hs y.toAdd`. Take `⟨a, rfl⟩` from `units_to_invariants_prime_surjective p K x`.

Conclude with `⟨a.toMul, hx⟩`. Establish `hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range`. Use extensionality with `a`. Rewrite using `[MonoidHom.mem_ker, MonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Establish `ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0` using `ha`. Take `⟨y, hy⟩` from `(e2 _).1 ha'`. Take `⟨b, rfl⟩` from `units_to_invariants_prime_surjective p K y`. Use `⟨b.toMul, ?_⟩` and prove the remaining obligations.

Use `(power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy` as an intermediate fact. Conclude with `units_to_invariants_prime_injective p K this`. Introduce and unpack `⟨b, rfl⟩ show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0`. Conclude with `(e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩`. Establish `E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho)` using `(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)`.

Conclude with `⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩`.
-/
theorem h1_roots_of_unity_equiv_of_h1_subsingleton (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n]
    (h90 : Subsingleton (H1 (kbarRep p K))) :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) := by
  obtain ⟨ζ, hζ⟩ := exists_primitive_unit p n
  obtain ⟨δ₀, δ₁, -, -, -, -, e2, e3, -⟩ :=
    low_degree_long_exact_sequence ℤ (GK p K) (muT p K n) (kT p K) (kT p K) (iP K hζ) (pP p K n) (adm K hζ)
  have h90' : Subsingleton (ReciprocityTheory.Gal.H1 (kT p K).rho) := h90
  have hs : Function.Surjective δ₀ := fun y => (e3 y).1 (Subsingleton.elim _ _)
  let ψ : Kˣ →* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    AddMonoidHom.toMultiplicativeRight (δ₀.toAddMonoidHom.comp (unitsToInvariants' p K))
  have hψ : ∀ a : Kˣ, ψ a = Multiplicative.ofAdd (δ₀ (unitsToInvariants' p K (Additive.ofMul a))) := fun a => rfl
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hs y.toAdd
    obtain ⟨a, rfl⟩ := units_to_invariants_prime_surjective p K x
    exact ⟨a.toMul, hx⟩
  have hker : ψ.ker = (powMonoidHom n : Kˣ →* Kˣ).range := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro ha
      have ha' : δ₀ (unitsToInvariants' p K (Additive.ofMul a)) = 0 := ha
      obtain ⟨y, hy⟩ := (e2 _).1 ha'
      obtain ⟨b, rfl⟩ := units_to_invariants_prime_surjective p K y
      refine ⟨b.toMul, ?_⟩
      have := (power_map_h0_unitsToInvariants p K n b.toMul).symm.trans hy
      exact units_to_invariants_prime_injective p K this
    · rintro ⟨b, rfl⟩
      show δ₀ (unitsToInvariants' p K (Additive.ofMul (b ^ n))) = 0
      exact (e2 _).2 ⟨_, power_map_h0_unitsToInvariants p K n b⟩
  have E1 : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range ≃* Multiplicative (ReciprocityTheory.Gal.H1 (muT p K n).rho) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
  exact ⟨(h1ScalarEquiv (charRep (cycK p K n)) (muRep p K n) fun _ _ => rfl).trans (MulEquiv.toAdditiveLeft E1).symm⟩

/- English proof (translation)
The claim follows from `h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)`.
-/
theorem h1_roots_of_unity_equiv_units_quot_pow (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) [NeZero n] :
    Nonempty (H1 (charRep (cycK p K n)) ≃+ Additive (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)) :=
  h1_roots_of_unity_equiv_of_h1_subsingleton p K n (h1_kbarRep_subsingleton p K)

end ReciprocityTheory.DiscreteGroups.LocalClassField
