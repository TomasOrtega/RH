import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeHomSectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeEtaleSheafSectionLocallyFiniteCombinationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BigEtaleModuleSheafMonoEpiIffSectionsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.FreeMonoEpi

/- English proof (translation)
Rewrite using `[NatTrans.mono_iff_mono_app]`. Introduce `U`. Rewrite using `[ModuleCat.mono_iff_injective]`. Establish `hf : Function.Injective (f.app U)` using `(mono_iff_injective (f.app U)).1 inferInstance`. Establish `hu : Function.Injective (uliftFunctor.{1}.map (f.app U))`.

Introduce `a b h`. Consider the cases of `a`. Consider the cases of `b`. Conclude with `congrArg ULift.up (hf (congrArg ULift.down h))`. Conclude with `Finsupp.mapDomain_injective hu`.
-/
theorem freeP_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((freeP R).map f) := by
  rw [NatTrans.mono_iff_mono_app]
  intro U
  rw [ModuleCat.mono_iff_injective]
  have hf : Function.Injective (f.app U) := (mono_iff_injective (f.app U)).1 inferInstance
  have hu : Function.Injective (uliftFunctor.{1}.map (f.app U)) := by
    intro a b h; cases a; cases b; exact congrArg ULift.up (hf (congrArg ULift.down h))
  exact Finsupp.mapDomain_injective hu

/- English proof (translation)
Use `haveI := freeP_map_mono R f`. Conclude with `(presheafToSheaf _ _).map_mono ((freeP R).map f)`.
-/
theorem free_map_mono (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) [Mono f] : Mono ((free R).map f) := by
  haveI := freeP_map_mono R f
  exact (presheafToSheaf _ _).map_mono ((freeP R).map f)

/- English proof (translation)
Simplify using `[Sec.res]`.
-/
theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (a : Sec F U) :
    Sec.res (k ≫ g) a = Sec.res k (Sec.res g a) := by
  simp [Sec.res]

/- English proof (translation)
Use `congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)` as an intermediate fact. Simplify `this` using `[Sec.map, Sec.res]`.
-/
theorem map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (a : Sec F U) :
    Sec.map φ (Sec.res g a) = Sec.res g (Sec.map φ a) := by
  have := congrArg (fun h => ModuleCat.Hom.hom h a) (φ.hom.naturality g.op)
  simpa [Sec.map, Sec.res] using this

abbrev gsum (R : Type) [CommRing R] (P : PSh) (V : Scheme.{0}) (c : P.obj (op V) →₀ ULift.{1} R) : Sec ((free R).obj P) V :=
  c.sum fun x r => r • freeGen R P V x

/- English proof (translation)
Simplify using `only [gsum, Sec.res, map_finsuppSum, map_smul]`. Use `Finsupp.sum_congr fun x _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `(GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.1 W V k x`.
-/
theorem res_gsum (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = c.sum fun x r => r • freeGen R P W (P.map k.op x) := by
  simp only [gsum, Sec.res, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.1 W V k x

/- English proof (translation)
Rewrite using `[res_gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : P.obj (op W)) (r : ULift.{1} R) => r • freeGen R P W x) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`.
-/
theorem res_gsum' (R : Type) [CommRing R] (P : PSh) {W V : Scheme.{0}} (k : W ⟶ V) (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.res k (gsum R P V c) = gsum R P W (Finsupp.mapDomain (P.map k.op) c) := by
  rw [res_gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : P.obj (op W)) (r : ULift.{1} R) => r • freeGen R P W x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]

/- English proof (translation)
Rewrite using `[gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : Q.obj (op V)) (r : ULift.{1} R) => r • freeGen R Q V x) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Simplify using `only [Sec.map, map_finsuppSum, map_smul]`. Use `Finsupp.sum_congr fun x _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `(GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f V x`.
-/
theorem map_gsum (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q) {V : Scheme.{0}} (c : P.obj (op V) →₀ ULift.{1} R) :
    Sec.map ((free R).map f) (gsum R P V c) = gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) := by
  rw [gsum, gsum, Finsupp.sum_mapDomain_index (h := fun (x : Q.obj (op V)) (r : ULift.{1} R) => r • freeGen R Q V x)
    (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Sec.map, map_finsuppSum, map_smul]
  refine Finsupp.sum_congr fun x _ => ?_
  congr 1
  exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f V x

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h`.
-/
theorem loc_all {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : ∀ V g, P V g) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.1 U P h

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ`.
-/
theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) :
    Loc U Q :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.1 U P Q h hPQ

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h`.
-/
theorem loc_trans {U : Scheme.{0}} {P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop}
    (h : Loc U fun V g => Loc V fun W k => P W (k ≫ g)) : Loc U P :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.1 U P h

/- English proof (translation)
The claim follows from `GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h`.
-/
theorem loc_fin {U : Scheme.{0}} {ι : Type} [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g :=
  GlobalTheory.T.etaleLocal_property_calculus_rules.2.2.2.2.2.1 U ι P h

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.2.1]`. Introduce `U b`. Apply `loc_trans` to reduce the goal to its premises. Use `loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q U).1 b) ?_` and prove the remaining obligations. Introduce and unpack `V g ⟨c, hc⟩`.

Establish `hl : Loc V fun W k => ∀ i : c.support, ∃ x, f.app (op W) x = Q.map k.op i.1` using `loc_fin (fun i : c.support => fun W k => ∃ x, f.app (op W) x = Q.map k.op i.1) (fun i => hs V i.1)`. Use `loc_mono hl ?_` and prove the remaining obligations. Introduce `W k hk`. Use `choose x hx using hk`. Use `⟨∑ i : c.support, c i.1 • freeGen R P W (x i), ?_⟩` and prove the remaining obligations.

Establish `e1 : Sec.map ((free R).map f) (∑ i : c.support, c i.1 • freeGen R P W (x i)) = ∑ i : c.support, c i.1 • freeGen R Q W (Q.map k.op i.1)`. Simplify using `only [Sec.map, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`. Rewrite using `[← hx i]`.

Conclude with `(GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f W (x i)`. Rewrite using `[e1, res_comp, hc, res_gsum, Finsupp.sum]`. Conclude with `Finset.sum_coe_sort c.support (fun y => c y • freeGen R Q W (Q.map k.op y))`.
-/
theorem free_map_epi (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hs : ∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) : Epi ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.2.1]
  intro U b
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q U).1 b) ?_
  rintro V g ⟨c, hc⟩
  have hl : Loc V fun W k => ∀ i : c.support, ∃ x, f.app (op W) x = Q.map k.op i.1 :=
    loc_fin (fun i : c.support => fun W k => ∃ x, f.app (op W) x = Q.map k.op i.1) (fun i => hs V i.1)
  refine loc_mono hl ?_
  intro W k hk
  choose x hx using hk
  refine ⟨∑ i : c.support, c i.1 • freeGen R P W (x i), ?_⟩
  have e1 : Sec.map ((free R).map f) (∑ i : c.support, c i.1 • freeGen R P W (x i)) =
      ∑ i : c.support, c i.1 • freeGen R Q W (Q.map k.op i.1) := by
    simp only [Sec.map, map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hx i]; exact (GlobalTheory.T.free_sections_ext_res_map R P ((free R).obj P)).2.2.2 Q f W (x i)
  rw [e1, res_comp, hc, res_gsum, Finsupp.sum]
  exact Finset.sum_coe_sort c.support (fun y => c y • freeGen R Q W (Q.map k.op y))

/- English proof (translation)
Establish `hl : Loc W fun W' k => ∀ i : d.support × d.support, f.app (op W) i.1.1 = f.app (op W) i.2.1 → P.map k.op i.1.1 = P.map k.op i.2.1` using `loc_fin _ fun i => by`. Distinguish the cases in `h : f.app (op W) i.1.1 = f.app (op W) i.2.1`. Conclude with `loc_mono (hi W _ _ h) fun _ _ e _ => e`. Conclude with `loc_all fun _ _ e => absurd e h`. Use `loc_mono hl ?_` and prove the remaining obligations.

Introduce `W' k hk`. Break down `d.support.eq_empty_or_nonempty with h0 | ⟨x0, _⟩` into its components or cases. Rewrite using `[Finsupp.support_eq_empty.1 h0, Finsupp.mapDomain_zero]`. Set `h : Q.obj (op W) → P.obj (op W')` to `fun y => if hy : ∃ x ∈ d.support, f.app (op W) x = y then P.map k.op hy.choose else P.map k.op x0`. Establish `e : Finsupp.mapDomain (P.map k.op) d = Finsupp.mapDomain (h ∘ f.app (op W)) d`.

Apply `Finsupp.mapDomain_congr` to reduce the goal to its premises. Introduce `x hx`. Establish `hy : ∃ x' ∈ d.support, f.app (op W) x' = f.app (op W) x` using `⟨x, hx, rfl⟩`. Use `show _ = h (f.app (op W) x)`. Simplify using `only [h, dif_pos hy]`.

Conclude with `hk (⟨x, hx⟩, ⟨hy.choose, hy.choose_spec.1⟩) hy.choose_spec.2.symm`. Rewrite using `[e, Finsupp.mapDomain_comp, hd, Finsupp.mapDomain_zero]`.
-/
theorem loc_kill {R : Type} [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x')
    {W : Scheme.{0}} (d : P.obj (op W) →₀ ULift.{1} R) (hd : Finsupp.mapDomain (f.app (op W)) d = 0) :
    Loc W fun _ k => Finsupp.mapDomain (P.map k.op) d = 0 := by
  classical
  have hl : Loc W fun W' k => ∀ i : d.support × d.support,
      f.app (op W) i.1.1 = f.app (op W) i.2.1 → P.map k.op i.1.1 = P.map k.op i.2.1 :=
    loc_fin _ fun i => by
      by_cases h : f.app (op W) i.1.1 = f.app (op W) i.2.1
      · exact loc_mono (hi W _ _ h) fun _ _ e _ => e
      · exact loc_all fun _ _ e => absurd e h
  refine loc_mono hl ?_
  intro W' k hk
  rcases d.support.eq_empty_or_nonempty with h0 | ⟨x0, _⟩
  · rw [Finsupp.support_eq_empty.1 h0, Finsupp.mapDomain_zero]
  let h : Q.obj (op W) → P.obj (op W') := fun y =>
    if hy : ∃ x ∈ d.support, f.app (op W) x = y then P.map k.op hy.choose else P.map k.op x0
  have e : Finsupp.mapDomain (P.map k.op) d = Finsupp.mapDomain (h ∘ f.app (op W)) d := by
    apply Finsupp.mapDomain_congr
    intro x hx
    have hy : ∃ x' ∈ d.support, f.app (op W) x' = f.app (op W) x := ⟨x, hx, rfl⟩
    show _ = h (f.app (op W) x)
    simp only [h, dif_pos hy]
    exact hk (⟨x, hx⟩, ⟨hy.choose, hy.choose_spec.1⟩) hy.choose_spec.2.symm
  rw [e, Finsupp.mapDomain_comp, hd, Finsupp.mapDomain_zero]

/- English proof (translation)
Rewrite using `[(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.1]`. Introduce `U a ha`. Apply `loc_trans` to reduce the goal to its premises. Use `loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 a) ?_` and prove the remaining obligations. Introduce and unpack `V g ⟨c, hc⟩`.

Establish `h0 : gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) = 0`. Rewrite using `[← map_gsum, show gsum R P V c = Sec.res g a from hc.symm, map_res, ha]`. Simplify using `[Sec.res]`. Apply `loc_trans` to reduce the goal to its premises. Use `loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q V).2 _ h0) ?_` and prove the remaining obligations.

Introduce `W k hk`. Establish `hd : Finsupp.mapDomain (f.app (op W)) (Finsupp.mapDomain (P.map k.op) c) = 0`. Rewrite using `[← Finsupp.mapDomain_comp]`. Rewrite using `[show (f.app (op W) ∘ P.map k.op) = (Q.map k.op ∘ f.app (op V)) from`. Use function extensionality and compare the values at `fun x => FunctorToTypes.naturality f k.op x]`.

Rewrite using `[Finsupp.mapDomain_comp]`. Conclude with `hk`. Use `loc_mono (loc_kill f hi _ hd) ?_` and prove the remaining obligations. Introduce `W' k' hk'`. Rewrite using `[res_comp, res_comp, hc, res_gsum', res_gsum', hk']`.

Simplify using `[gsum]`.
-/
theorem free_map_mono_of_loc (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q)
    (hi : ∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') :
    Mono ((free R).map f) := by
  rw [(GlobalTheory.T.bigEtaleModuleSheaf_mono_epi_iff_sections R ((free R).map f)).2.1]
  intro U a ha
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R P U).1 a) ?_
  rintro V g ⟨c, hc⟩
  have h0 : gsum R Q V (Finsupp.mapDomain (f.app (op V)) c) = 0 := by
    rw [← map_gsum, show gsum R P V c = Sec.res g a from hc.symm, map_res, ha]; simp [Sec.res]
  apply loc_trans
  refine loc_mono ((GlobalTheory.T.freeEtaleSheaf_section_locally_finite_combination R Q V).2 _ h0) ?_
  intro W k hk
  have hd : Finsupp.mapDomain (f.app (op W)) (Finsupp.mapDomain (P.map k.op) c) = 0 := by
    rw [← Finsupp.mapDomain_comp]
    rw [show (f.app (op W) ∘ P.map k.op) = (Q.map k.op ∘ f.app (op V)) from
      funext fun x => FunctorToTypes.naturality f k.op x]
    rw [Finsupp.mapDomain_comp]; exact hk
  refine loc_mono (loc_kill f hi _ hd) ?_
  intro W' k' hk'
  rw [res_comp, res_comp, hc, res_gsum', res_gsum', hk']
  simp [gsum]

end GlobalTheory.EtC.FreeMonoEpi

namespace GlobalTheory.EtC

open GlobalTheory.EtC.FreeMonoEpi in

/- English proof (translation)
Introduce `R _ P Q f`. Use `⟨fun _ => free_map_mono R f, free_map_epi R f, fun hs hi => ?_⟩` and prove the remaining obligations. Use `haveI := free_map_epi R f hs`. Use `haveI := free_map_mono_of_loc R f hi`. Conclude with `isIso_of_mono_of_epi _`.
-/
theorem free_map_mono_epi_iso : ∀ (R : Type) [CommRing R] {P Q : PSh} (f : P ⟶ Q), (Mono f → Mono ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → Epi ((free R).map f)) ∧ ((∀ U (y : Q.obj (op U)), Loc U fun V g => ∃ x, f.app (op V) x = Q.map g.op y) → (∀ U (x x' : P.obj (op U)), f.app (op U) x = f.app (op U) x' → Loc U fun _ g => P.map g.op x = P.map g.op x') → IsIso ((free R).map f)) := by
  intro R _ P Q f
  refine ⟨fun _ => free_map_mono R f, free_map_epi R f, fun hs hi => ?_⟩
  haveI := free_map_epi R f hs
  haveI := free_map_mono_of_loc R f hi
  exact isIso_of_mono_of_epi _

end GlobalTheory.EtC
end
