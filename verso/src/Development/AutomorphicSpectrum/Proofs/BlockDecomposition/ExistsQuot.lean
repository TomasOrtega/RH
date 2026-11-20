import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.MapUSharp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationOfValuationModSquare
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallinePointUniversalLiftStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.TowerAct

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d}

def val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : T.1.A :=
  PAlg.Hom.f φ.1 (𝒯.c k 0).val

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_comp (𝒯 : Tower κ s) {T T' : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (ψ : T ⟶ T') (k : Fin d) :
    val 𝒯 (φ ≫ ψ) k = PAlg.Hom.f ψ.1 (val 𝒯 φ k) := rfl

/- English proof (translation)
Rewrite using `[val, ← mapU_sharp]`. Conclude with `congrArg (mapU φ.1) (𝒯.c_sharp k)`.
-/
theorem sharp_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    T.1.sharp (val 𝒯 φ k) = mapU φ.1 (𝒯.g (s.T k)) := by
  rw [val, ← mapU_sharp]
  exact congrArg (mapU φ.1) (𝒯.c_sharp k)

def valU (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) : (T.1.A)ˣ :=
  Units.map (PAlg.Hom.f φ.1).toMonoidHom (𝒯.c k 0)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem valU_val (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    ((valU 𝒯 φ k : (T.1.A)ˣ) : T.1.A) = val 𝒯 φ k := rfl

/- English proof (translation)
Take `⟨g, -, hg, huniq⟩` from `GlobalTheory.T.crystalline_point_universal_lift 𝒯 T`. Establish `hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k)` using `fun k => by`. Rewrite using `[sharp_val]`. Conclude with `RingHom.congr_fun (hg φ) _`. Take `⟨χ, -, hχ⟩` from `huniq (fun k => val 𝒯 φ k) hu`.

Conclude with `(hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm`.
-/
theorem hom_ext (𝒯 : Tower κ s) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T)
    (h : ∀ k, val 𝒯 φ k = val 𝒯 ψ k) : φ = ψ := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, -, hχ⟩ := huniq (fun k => val 𝒯 φ k) hu
  exact (hχ φ (fun k => rfl)).trans (hχ ψ (fun k => (h k).symm)).symm

/- English proof (translation)
Establish `hx : Units.map T.1.sharp x.1 = 1` using `x.2`. Conclude with `congrArg Units.val hx`.
-/
theorem sharp_mem (ε : Eps l) {T : (F.pt κ).Elements} (x : (epsU ε (F.pt κ)).U T) :
    T.1.sharp ((x.1 : (T.1.A)ˣ) : T.1.A) = 1 := by
  have hx : Units.map T.1.sharp x.1 = 1 := x.2
  exact congrArg Units.val hx

/- English proof (translation)
Take `⟨g, -, hg, huniq⟩` from `GlobalTheory.T.crystalline_point_universal_lift 𝒯 T`. Establish `hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k)` using `fun k => by`. Rewrite using `[map_mul, sharp_mem ε (a k), one_mul, sharp_val]`. Conclude with `RingHom.congr_fun (hg φ) _`. Take `⟨χ, hχ, -⟩` from `huniq _ hu`.

Conclude with `⟨χ, fun k => hχ k⟩`.
-/
theorem exists_act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) :
    ∃ ψ : 𝒯.obj ⟶ T, ∀ k, val 𝒯 ψ k = ((a k).1 : T.1.A) * val 𝒯 φ k := by
  obtain ⟨g, -, hg, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hu : ∀ k, T.1.sharp (((a k).1 : T.1.A) * val 𝒯 φ k) = g (s.T k) := fun k => by
    rw [map_mul, sharp_mem ε (a k), one_mul, sharp_val]
    exact RingHom.congr_fun (hg φ) _
  obtain ⟨χ, hχ, -⟩ := huniq _ hu
  exact ⟨χ, fun k => hχ k⟩

def act (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) : 𝒯.obj ⟶ T :=
  (exists_act 𝒯 ε a φ).choose

/- English proof (translation)
The claim follows from `(exists_act 𝒯 ε a φ).choose_spec k`.
-/
theorem act_val (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d) :
    val 𝒯 (act 𝒯 ε a φ) k = ((a k).1 : T.1.A) * val 𝒯 φ k :=
  (exists_act 𝒯 ε a φ).choose_spec k

/- English proof (translation)
Take `⟨g, -, hg, -⟩` from `GlobalTheory.T.crystalline_point_universal_lift 𝒯 T`. Establish `hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k)` using `fun χ k => by`. Rewrite using `[sharp_val]`. Conclude with `RingHom.congr_fun (hg χ) _`. Use `⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩` and prove the remaining obligations.

Use `show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, mul_inv_eq_one]`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]`. Use `show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k`.

Rewrite using `[← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]`.
-/
theorem exists_quot (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements} (φ ψ : 𝒯.obj ⟶ T) :
    ∃ a : Fin d → (epsU ε (F.pt κ)).U T, ∀ k, ((a k).1 : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k := by
  obtain ⟨g, -, hg, -⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 T
  have hs : ∀ (χ : 𝒯.obj ⟶ T) k, T.1.sharp (val 𝒯 χ k) = g (s.T k) := fun χ k => by
    rw [sharp_val]
    exact RingHom.congr_fun (hg χ) _
  refine ⟨fun k => ⟨valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹, ?_⟩, fun k => ?_⟩
  · show Units.map T.1.sharp (valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹) = 1
    rw [map_mul, map_inv, mul_inv_eq_one]
    apply Units.ext
    rw [Units.coe_map, Units.coe_map, valU_val, valU_val, hs ψ k, hs φ k]
  · show ((valU 𝒯 ψ k * (valU 𝒯 φ k)⁻¹ : (T.1.A)ˣ) : T.1.A) * val 𝒯 φ k = val 𝒯 ψ k
    rw [← valU_val 𝒯 φ k, ← Units.val_mul, inv_mul_cancel_right, valU_val]

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `h1` using `act_val 𝒯 ε a φ k`. Rewrite `h1` using `[h, act_val, ← valU_val 𝒯 φ k]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Units.ext` to reduce the goal to its premises.

Conclude with `((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm`.
-/
theorem act_unique (𝒯 : Tower κ s) (ε : Eps l) {T : (F.pt κ).Elements}
    (a b : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (h : act 𝒯 ε a φ = act 𝒯 ε b φ) : a = b := by
  funext k
  have h1 := act_val 𝒯 ε a φ k
  rw [h, act_val, ← valU_val 𝒯 φ k] at h1
  apply Subtype.ext
  apply Units.ext
  exact ((valU 𝒯 φ k).isUnit.mul_left_inj).1 h1.symm

/- English proof (translation)
Introduce `l _ O _ F κ d s 𝒯 ε`. Use `⟨{ act := fun a φ => act 𝒯 ε a φ act_one := fun c => hom_ext 𝒯 _ _ fun k => by` and prove the remaining obligations. Rewrite using `[act_val]`. Conclude with `one_mul _`. Use `act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by`.

Rewrite using `[act_val, act_val, act_val, ← mul_assoc]`. Both sides reduce to the same expression. Use `act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by`. Rewrite using `[val_comp, act_val, act_val, val_comp, map_mul]`. Both sides reduce to the same expression.

Use `ne := fun t => by`. Take `⟨g, -, -, huniq⟩` from `GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)`. Use `choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))`. Take `⟨χ, -, -⟩` from `huniq u hu`. Conclude with `⟨χ⟩`.

Use `trans := fun t c c' => by`. Take `⟨a, ha⟩` from `exists_quot 𝒯 ε c c'`. Establish `hac : act 𝒯 ε a c = c'` using `hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]`. Conclude with `⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩`. Introduce `T a φ k`.

Conclude with `act_val 𝒯 ε a φ k`.
-/
theorem tower_act : ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F : Fn O} {κ : O →+* OC l} {d : ℕ} {s : F.Small d} (𝒯 : Tower κ s) (ε : Eps l), ∃ A : Act (jE (F.pt κ)) (epsU ε (F.pt κ)) d 𝒯.obj, ∀ (T : (F.pt κ).Elements) (a : Fin d → (epsU ε (F.pt κ)).U T) (φ : 𝒯.obj ⟶ T) (k : Fin d), PAlg.Hom.f (A.act a φ).1 (𝒯.c k 0).val = ((a k).1 : T.1.A) * PAlg.Hom.f φ.1 (𝒯.c k 0).val := by
  intro l _ O _ F κ d s 𝒯 ε
  refine ⟨{ act := fun a φ => act 𝒯 ε a φ
            act_one := fun c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val]
              exact one_mul _
            act_mul := fun a b c => hom_ext 𝒯 _ _ fun k => by
              rw [act_val, act_val, act_val, ← mul_assoc]
              rfl
            act_comp := fun a c φ => hom_ext 𝒯 _ _ fun k => by
              rw [val_comp, act_val, act_val, val_comp, map_mul]
              rfl
            ne := fun t => by
              obtain ⟨g, -, -, huniq⟩ := GlobalTheory.T.crystalline_point_universal_lift 𝒯 ((jE (F.pt κ)).obj t)
              choose u hu using fun k => PAlg.IsTest.sharp_surjective t.1.property (g (s.T k))
              obtain ⟨χ, -, -⟩ := huniq u hu
              exact ⟨χ⟩
            trans := fun t c c' => by
              obtain ⟨a, ha⟩ := exists_quot 𝒯 ε c c'
              have hac : act 𝒯 ε a c = c' := hom_ext 𝒯 _ _ fun k => by rw [act_val, ha]
              exact ⟨a, hac, fun b hb => act_unique 𝒯 ε b a c (hb.trans hac.symm)⟩ }, ?_⟩
  intro T a φ k
  exact act_val 𝒯 ε a φ k

end GlobalTheory.CompanionTheory.TowerAct
