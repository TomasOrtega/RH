import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.KumPowProof

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `w hw`. Rewrite `hw` using `[pow_zero, one_mul]`. Rewrite using `[Units.ext hw, zero_smul, add_zero]`.

Consider the case `succ k ih`. Introduce `w hw`. Establish `hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v)` using `by rw [hw]; ring`. Take `⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v)` from `isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)`. Rewrite using `[ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]`.
-/
theorem isKum_pow {q : ℕ} {t : ∀ U : Scheme.{0}, (Γ(U, ⊤))ˣ → Sec ((res _ (tw q 1)).X 0) U} (ht : IsKum q t)
    {U : Scheme.{0}} (ζ : Prim q Γ(U, ⊤)) (v : (Γ(U, ⊤))ˣ) (k : ℕ) :
    ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ k * v → t U w = t U v + k • resGen 1 ζ := by
  induction k with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    rw [Units.ext hw, zero_smul, add_zero]
  | succ k ih =>
    intro w hw
    have hw' : (w : Γ(U, ⊤)) = ζ.1 * (ζ.1 ^ k * v) := by rw [hw]; ring
    obtain ⟨z, hz⟩ : IsUnit (ζ.1 ^ k * v) := isUnit_of_mul_isUnit_right (hw' ▸ w.isUnit)
    rw [ht.2 U ζ z w (by rw [hw', hz]), ih z hz, succ_nsmul, add_assoc]

/- English proof (translation)
Establish `h` using `φ.hom.naturality g.op`. Conclude with `(congrArg (fun m => m.hom x) h).symm`.
-/
theorem res_smap {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have h := φ.hom.naturality g.op
  exact (congrArg (fun m => m.hom x) h).symm

/- English proof (translation)
Introduce `hL _ hK _ hKum q _ U ζ f r v hr`. Establish `ht : IsKum q (kumT q)` using `hKum q`. Establish `hq : IsUnit (q : Γ(U, ⊤))` using `ζ.2.1`. Take `⟨W, j, hf, -, -, hG⟩` from `hL U (ZMod q) f`. Take `⟨y, -, huniq⟩` from `hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))`.

Use `(huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm` and prove the remaining obligations. Establish `hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val` using `hr (W a) (j a) a (hf a)`. Establish `hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ)` using `(hK q 1 U ζ f).1 (W a) (j a) a (hf a)`. Establish `hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q))` using `ULift.ext _ _ (by change a = a.val • (1 : ZMod q); simp)`. Establish `hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ)`.

Rewrite using `[hlc, hup, smul_assoc, one_smul]`. Establish `hkey` using `isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by`. Express the relevant statement in the definitionally equal form `(j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val`. Rewrite using `[map_mul, hra])`. Establish `e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v))` using `ht.1 _ _ (j a) _ hq`.

Establish `e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v)` using `ht.1 _ _ (j a) _ hq`. Establish `e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ)`. Rewrite using `[res_smap, hsm]`. Conclude with `map_nsmul _ _ _`. Establish `e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f))` using `map_add _ _ _`.

Rewrite using `[e0, e1, e2, e3, hkey]`.
-/
theorem kumPow : LcCover → RepRoot → KapSpec → PrimAlg → KumPow := by
  intro hL _ hK _ hKum q _ U ζ f r v hr
  have ht : IsKum q (kumT q) := hKum q
  have hq : IsUnit (q : Γ(U, ⊤)) := ζ.2.1
  obtain ⟨W, j, hf, -, -, hG⟩ := hL U (ZMod q) f
  obtain ⟨y, -, huniq⟩ := hG (ZMod q) ((res _ (tw q 1)).X 0) (fun a => Sec.res (j a) (kumT q U (r * v)))
  refine (huniq _ fun a => rfl).trans (huniq _ fun a => ?_).symm
  have hra : (j a).appTop.hom r.val = (primRes (j a) ζ).1 ^ a.val := hr (W a) (j a) a (hf a)
  have hlc : Sec.res (j a) (kap 1 ζ f) = (ULift.up a : ULift.{1} (ZMod q)) • twGen 1 (primRes (j a) ζ) :=
    (hK q 1 U ζ f).1 (W a) (j a) a (hf a)
  have hup : (ULift.up a : ULift.{1} (ZMod q)) = a.val • (1 : ULift.{1} (ZMod q)) :=
    ULift.ext _ _ (by change a = a.val • (1 : ZMod q); simp)
  have hsm : Sec.res (j a) (kap 1 ζ f) = a.val • twGen 1 (primRes (j a) ζ) := by
    rw [hlc, hup, smul_assoc, one_smul]
  have hkey := isKum_pow ht (primRes (j a) ζ) (Units.map (j a).appTop.hom.toMonoidHom v) a.val
    (Units.map (j a).appTop.hom.toMonoidHom (r * v)) (by
      change (j a).appTop.hom (r.val * v.val) = _ * (j a).appTop.hom v.val
      rw [map_mul, hra])
  have e1 : Sec.res (j a) (kumT q U (r * v)) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom (r * v)) :=
    ht.1 _ _ (j a) _ hq
  have e2 : Sec.res (j a) (kumT q U v) = kumT q (W a) (Units.map (j a).appTop.hom.toMonoidHom v) :=
    ht.1 _ _ (j a) _ hq
  have e3 : Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) = a.val • resGen 1 (primRes (j a) ζ) := by
    rw [res_smap, hsm]
    exact map_nsmul _ _ _
  have e0 : Sec.res (j a) (kumT q U v + Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) =
      Sec.res (j a) (kumT q U v) + Sec.res (j a) (Sec.map (resι _ (tw q 1)) (kap 1 ζ f)) := map_add _ _ _
  rw [e0, e1, e2, e3, hkey]

end GlobalTheory.CompanionTheory.KumPowProof
