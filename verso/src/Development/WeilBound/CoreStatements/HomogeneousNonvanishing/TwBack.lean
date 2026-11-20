import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRankStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsSectionLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B}

/- English proof (translation)
Establish `hM : (l.M : 𝓞 E) ∈ l.Mb`. Establish `h` using `Ideal.mem_span_singleton_self (l.M : 𝓞 E)`. Rewrite `h` using `[← l.prod]`. Conclude with `Ideal.mul_le_left h`. Rewrite using `[o.eta_add, o.eta_ker (l.M • e), _root_.mul_one]`.

Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul hM trivial`.
-/
theorem tb_eta (o : Obj D l b s) (x e : D.La) : o.eta (x + l.M • e) = o.eta x := by
  have hM : (l.M : 𝓞 E) ∈ l.Mb := by
    have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
    rw [← l.prod] at h
    exact Ideal.mul_le_left h
  rw [o.eta_add, o.eta_ker (l.M • e), _root_.mul_one]
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul hM trivial

/- English proof (translation)
Rewrite using `[o.etaA_add, o.etaA_ker, _root_.mul_one]`.
-/
theorem tb_etaA (o : Obj D l b s) (x e : D.La) : o.etaA (x + l.A • e) = o.etaA x := by
  rw [o.etaA_add, o.etaA_ker, _root_.mul_one]

/- English proof (translation)
Take `⟨m, hm⟩` from `GlobalTheory.T.sab_map_id E H S t`. Use `⟨⟨m.cm, m.cart, m.base, fun a => ?_, m.lin⟩, hm⟩` and prove the remaining obligations. Use `m.act a` as an intermediate fact. Use `show (t.act.act (g.s (g'.s a))).left ≫ m.cm.F = _`. Rewrite using `[h]`.

Conclude with `this`.
-/
theorem tb_map (t : SAB H S) (g g' : HostAut H) (h : ∀ a, g.s (g'.s a) = a) :
    ∃ m : SABMap (twistSAB (twistSAB t g) g') t (𝟙 S), m.φ = 𝟙 t.G.left := by
  obtain ⟨m, hm⟩ := GlobalTheory.T.sab_map_id E H S t
  refine ⟨⟨m.cm, m.cart, m.base, fun a => ?_, m.lin⟩, hm⟩
  have := m.act a
  show (t.act.act (g.s (g'.s a))).left ≫ m.cm.F = _
  rw [h]
  exact this
end

/- English proof (translation)
Introduce `E _ _ _ H D g a`. Use `D.fin` as an intermediate fact. Use `D.proj` as an intermediate fact. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.twisted_module_finite_projective_rank (𝓞 E) g.s D.La`. Take `⟨f, hf1, hf2⟩` from `ProIso.exists_isInv (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) a`.

Establish `k1 : ∀ c, g.s (g.symm.s c) = c` using `fun c => RingOfIntegers.ext (g.σ.apply_symm_apply c)`. Establish `k2 : ∀ c, g.symm.s (g.s c) = c` using `fun c => RingOfIntegers.ext (g.σ.symm_apply_apply c)`. Set `a' : TwIso D g.symm` to `{ a := fun n => { toFun := fun x => f.a n x map_add' := fun x y => (f.a n).map_add x y map_smul' := fun c x => by`. Establish `e` using `(f.a n).map_smul (g.symm.s c) x`. Use `Eq.trans (congrArg (f.a n) ?_) e` and prove the remaining obligations.

Use `show c • x = g.s (g.symm.s c) • x`. Rewrite using `[k1] }`. Use `inj := f.inj`. Use `surj := f.surj`. Use `isom := f.isom`.

Use `compat := f.compat }`. Use `⟨a', fun l B _ b S s o => ⟨fun h h' => ?_, fun h h' => ?_⟩⟩` and prove the remaining obligations. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Take `⟨m, hm⟩` from `tb_map o.t g g.symm k1`. Use `⟨⟨m, fun x => ?_, fun x => ?_⟩⟩` and prove the remaining obligations.

Take `⟨e, he⟩` from `hf2 l.M hM x`. Establish `: o.eta (a.a l.M (f.a l.M x)) = o.eta x` using `(congrArg o.eta he).trans (tb_eta o x e)`. Conclude with `(congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)`. Take `⟨e, he⟩` from `hf2 l.A l.A_pos x`. Establish `: o.etaA (a.a l.A (f.a l.A x)) = o.etaA x` using `(congrArg o.etaA he).trans (tb_etaA o x e)`.

Conclude with `(congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Take `⟨m, hm⟩` from `tb_map o.t g.symm g k2`. Use `⟨⟨m, fun x => ?_, fun x => ?_⟩⟩` and prove the remaining obligations. Take `⟨e, he⟩` from `hf1 l.M hM x`.

Establish `: o.eta (f.a l.M (a.a l.M x)) = o.eta x` using `(congrArg o.eta he).trans (tb_eta o x e)`. Conclude with `(congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)`. Take `⟨e, he⟩` from `hf1 l.A l.A_pos x`. Establish `: o.etaA (f.a l.A (a.a l.A x)) = o.etaA x` using `(congrArg o.etaA he).trans (tb_etaA o x e)`. Conclude with `(congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)`.
-/
theorem tw_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H) (a : TwIso D g), ∃ a' : TwIso D g.symm, ∀ (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s), (∀ (h : TwOK o g a) (h' : TwOK (twistObj o g a h) g.symm a'), Nonempty (ObjMap (twistObj (twistObj o g a h) g.symm a' h') o (𝟙 S))) ∧ ∀ (h : TwOK o g.symm a') (h' : TwOK (twistObj o g.symm a' h) g a), Nonempty (ObjMap (twistObj (twistObj o g.symm a' h) g a h') o (𝟙 S)) := by
  intro E _ _ _ H D g a
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twisted_module_finite_projective_rank (𝓞 E) g.s D.La
  obtain ⟨f, hf1, hf2⟩ := ProIso.exists_isInv (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) a
  have k1 : ∀ c, g.s (g.symm.s c) = c := fun c => RingOfIntegers.ext (g.σ.apply_symm_apply c)
  have k2 : ∀ c, g.symm.s (g.s c) = c := fun c => RingOfIntegers.ext (g.σ.symm_apply_apply c)
  let a' : TwIso D g.symm :=
    { a := fun n =>
        { toFun := fun x => f.a n x
          map_add' := fun x y => (f.a n).map_add x y
          map_smul' := fun c x => by
            have e := (f.a n).map_smul (g.symm.s c) x
            refine Eq.trans (congrArg (f.a n) ?_) e
            show c • x = g.s (g.symm.s c) • x
            rw [k1] }
      inj := f.inj
      surj := f.surj
      isom := f.isom
      compat := f.compat }
  refine ⟨a', fun l B _ b S s o => ⟨fun h h' => ?_, fun h h' => ?_⟩⟩
  · have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    obtain ⟨m, hm⟩ := tb_map o.t g g.symm k1
    refine ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩
    · obtain ⟨e, he⟩ := hf2 l.M hM x
      have : o.eta (a.a l.M (f.a l.M x)) = o.eta x := (congrArg o.eta he).trans (tb_eta o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
    · obtain ⟨e, he⟩ := hf2 l.A l.A_pos x
      have : o.etaA (a.a l.A (f.a l.A x)) = o.etaA x := (congrArg o.etaA he).trans (tb_etaA o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
  · have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
    obtain ⟨m, hm⟩ := tb_map o.t g.symm g k2
    refine ⟨⟨m, fun x => ?_, fun x => ?_⟩⟩
    · obtain ⟨e, he⟩ := hf1 l.M hM x
      have : o.eta (f.a l.M (a.a l.M x)) = o.eta x := (congrArg o.eta he).trans (tb_eta o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)
    · obtain ⟨e, he⟩ := hf1 l.A l.A_pos x
      have : o.etaA (f.a l.A (a.a l.A x)) = o.etaA x := (congrArg o.etaA he).trans (tb_etaA o x e)
      exact (congrArg₂ (fun u v => u.left ≫ v) this hm).trans ((Category.comp_id _).trans (Category.id_comp _).symm)

end PositivityTheory.UnitarySelfGeneration
