module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2190
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.MulEqOneOfComb
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ZH GlobalTheory.ZH.RatModel GlobalTheory.CompHt

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem mul_eq_one_of_comb {K V : Type} [Field K] [AddCommGroup V] [Module K V] {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (c : Matrix (Fin n) (Fin N) K)
    (h : ∀ j, b j = ∑ k, c k j • ∑ i, g i k • b i) : g * c = 1 := by
  ext i j
  have e := congrArg (fun v => b.repr v i) (h j)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at e
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [mul_comm (g i _), ← e, eq_comm]

theorem sum_eq {K : Type} [Field K] (σ : K →+* ℂ) {N n : ℕ} {g : Matrix (Fin N) (Fin n) K}
    {c : Matrix (Fin n) (Fin N) K} (h : g * c = 1) (A : Matrix (Fin N) (Fin N) ℂ) (x : Fin N → ℂ) (a : Fin N) :
    ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j = ∑ m, A m a * x m := by
  have e : ∀ j m, ∑ k, σ (g j k) * σ (c k m) = if j = m then 1 else 0 := fun j m => by
    have := congrArg σ (congrFun (congrFun h j) m)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, map_sum, Matrix.one_apply, apply_ite σ, map_one, map_zero] at this
    simpa only [map_mul] using this
  calc ∑ k, (∑ m, σ (c k m) * A m a) * ∑ j, σ (g j k) * x j
      = ∑ j, ∑ m, (∑ k, σ (g j k) * σ (c k m)) * (A m a * x j) := by
        simp only [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by simp [e]

theorem isometric_fs {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (M : RatModel (𝓞 K) Ω) (L : HermLB M.s)
    (ev : V →ₗ[K] Ω) {W : Submodule (𝓞 K) V} (s : W → L.B.Sec) {e : L.B.ι → Ω}
    (hv : ∀ w : W, M.HasVal e (s w) (ev w)) (hW : Submodule.span K (W : Set V) = ⊤) {N n : ℕ}
    (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin n) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (c : Matrix (Fin n) (Fin N) K) (gw : Fin n → W) (hgw : ∀ k, (gw k : V) = ∑ j, g j k • b j)
    (hcb : ∀ j, b j = ∑ k, c k j • (gw k : V))
    (hφ : ∀ (σ : K →+* ℂ) (i : L.B.ι) (y : CxPts M.s (σ.comp (algebraMap (𝓞 K) K))),
      (L.φ (σ.comp (algebraMap (𝓞 K) K))).φ i y =
        Real.log (∑ a, ‖∑ k, (∑ m, σ (c k m) * A σ m a) * valR y.1 (L.B.U i) ((s (gw k)).f i)‖ ^ 2))
    (hs : ⨆ k, nonzeroLocus (s (gw k)) = ⊤) (Mt : (𝓞 K →+* ℂ) → Matrix (Fin n) (Fin n) ℂ) (hdet hcc)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ),
      ∑ a, ‖∑ k, Mt (σ.comp (algebraMap (𝓞 K) K)) k a * ∑ j, σ (g j k) * x j‖ ^ 2 = GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    (t : ℝ) :
    ((HermLB.fs M.s L.isLB (fun k => s (gw k)) hs Mt hdet hcc).shift (fun _ => t) (fun _ => rfl)).Isometric
      (L.shift (fun _ => t) (fun _ => rfl)) := by
  have hgc := mul_eq_one_of_comb b g c fun j => by simpa only [hgw] using hcb j
  refine HermLB.isometric_of_eqOn fun σ' l y hl => ?_
  obtain ⟨σ, rfl⟩ : ∃ σ : K →+* ℂ, σ.comp (algebraMap (𝓞 K) K) = σ' := ⟨_, GlobalTheory.TrueGeo.OfLattice.extEmb_comp σ'⟩
  replace hl : y ∈ ptsIn M.s _ (L.B.U l) := hl
  have hz := mem_ptsIn.1 hl
  obtain ⟨x, hx⟩ := PositivityTheory.Xgn.A_xgz_height_r_vol_up_model_nef.exists_coord y.2 ev (e l) b hW fun v hvW => by
    rw [← hv ⟨v, hvW⟩ l ⟨_, hz⟩]
    exact valF_mem_O hz _
  have hr : Set.range y.1 ⊆ L.B.U l := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 hl
  have hsk : ∀ k, valR y.1 (L.B.U l) ((s (gw k)).f l) = ∑ j, σ (g j k) * x j := fun k => by
    refine ((val_eq hr (hv (gw k) l ⟨_, hz⟩)).symm.trans (hx _)).trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hgw, b.repr_sum_self]
  refine congrArg (· + 2 * t) ((hφ σ l y).trans (Eq.trans ?_
    (Weight.fsBasis_φ L.isLB (fun k => s (gw k)) hs _ (hdet _) l y).symm))
  simp only [hsk, hMt, sum_eq σ hgc]
  rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)]

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.RootOriginFrameComparison
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

section Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω}


set_option backward.isDefEq.respectTransparency false in
theorem lat_act_of_model_rf (𝔐 : HodgeCpt Y SS y) (q : Cpt 𝔐.ξ) (x : 𝓞 E) (e : 𝔐.Li) (he : e ∈ 𝔐.M.lat q) :
    𝔐.ρ x e ∈ 𝔐.M.lat q := by
  have := 𝔐.t.act.hom x
  rw [GlobalTheory.CompanionTheory.Ar.LieModel.mem_lat_iff] at he ⊢
  obtain ⟨v, hv⟩ := he
  obtain ⟨ht, hpt⟩ := (GlobalTheory.CompanionTheory.Ar.LieModel.extends_iff _ _ _ _).mp hv
  refine ⟨v ≫ 𝔐.t.act.act x, (GlobalTheory.CompanionTheory.Ar.LieModel.extends_iff _ _ _ _).mpr ⟨?_, ?_⟩⟩
  · rw [GlobalTheory.CompanionTheory.Ar.LieTangent.isTanAt_iff] at ht ⊢
    rw [← Category.assoc, ht, CategoryTheory.MonObj.one_comp]
  · rw [𝔐.act x e, hpt, Category.assoc]

end Act


set_option backward.isDefEq.respectTransparency false in
theorem isUnit_int_of_inFibre_rf {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z)
    {p : ℕ} (hp : p.Prime) (hf : InFibre ξ p ⟨centre z, h⟩) {d : ℤ} (hd : ¬ (p : ℤ) ∣ d) : IsUnit (d : R) := by
  by_contra hnd
  unfold GlobalTheory.CompanionTheory.Ar.InFibre GlobalTheory.CompanionTheory.Ar.unitAt GlobalTheory.CompanionTheory.Ar.regAt at hf
  have key : ∀ {S : Type} [CommRing S] [IsLocalRing S], IsCoprime (p : ℤ) d →
      ¬ IsUnit (p : S) → ¬ IsUnit (d : S) → False := by
    intro S _ _ hpd hp' hd'
    obtain ⟨a, b, hab⟩ := hpd
    have h1 : (a : S) * (p : S) + (b : S) * (d : S) = 1 := by
      have := congrArg (Int.cast : ℤ → S) hab
      push_cast at this
      exact this
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h' | h'
    · exact hp' (isUnit_of_mul_isUnit_right h')
    · exact hd' (isUnit_of_mul_isUnit_right h')
  refine key (S := X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z))
    ((Nat.prime_iff_prime_int.mp hp).coprime_iff_not_dvd.mpr hd) ?_ ?_
  · rintro ⟨u, hu⟩
    apply hf
    have hgp : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (p : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)) = (p : Ω) :=
      map_natCast _ p
    have hmul : GlobalTheory.CompanionTheory.Ar.genMap ξ ⟨GlobalTheory.CompanionTheory.Ar.centre z, h⟩ (↑u⁻¹ : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)) * (p : Ω) = 1 := by
      rw [← hgp, ← map_mul, ← hu, Units.inv_mul, map_one]
    refine ⟨right_ne_zero_of_mul_eq_one hmul, RingHom.mem_range.mpr ⟨_, hgp⟩, RingHom.mem_range.mpr ⟨(↑u⁻¹ : X.presheaf.stalk (GlobalTheory.CompanionTheory.Ar.centre z)), ?_⟩⟩
    exact eq_inv_of_mul_eq_one_left hmul
  · intro hu
    exact hnd (by simpa using hu.map (Scheme.stalkClosedPointTo z).hom)

theorem fib_eq_lieEig_rf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  intro E _ _ _ H Dw l Xo c O _ β Y SS RM Sys Fx Or Fr A p _ z ev hz hval hgood la T io e y evT zT t hint zV hread
    hpS hdisc EC _ _ _ _ MC ρC hact s σ hσ
  have hp : p.Prime := Fact.out
  have hgen : IsCptGen Or.𝔐.ξ := Or.𝔐.tie.gen
  have hsm : Smooth Or.𝔐.t.G.hom := Or.𝔐.t.semi.smooth
  have h₀ : genPt Or.𝔐.ξ ⤳ centre zV := Or.𝔐.all _
  have h₁ : genPt Or.𝔐.ξ ⤳ centre (gen T zV) := Or.𝔐.all _
  have hF : InFibre Or.𝔐.ξ p ⟨centre zV, h₀⟩ :=
    GlobalTheory.T.root_origin_frame_nonarchimedean E H Dw l Xo c O β Y SS RM Sys Fx Or Fr A p z ev hz hval hgood la T io e y evT zT t hint zV hread
  have hV : Or.𝔐.V s ⟨centre zV, h₀⟩ = Or.𝔐.dR s ⟨centre zV, h₀⟩ :=
    Lat.patch_of_not SS _ _ fun r hr hfr =>
      Lat.not_inFibre_of_coprime _ ((Nat.coprime_primes hp (Or.𝔐.S_prime r hr)).2
        fun hne => hpS (hne ▸ hr)) hF hfr
  obtain ⟨ev', hev1, hev2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val Or.𝔐.X Or.𝔐.t.G RM.Ω Or.𝔐.ξ Or.𝔐.Li Or.𝔐.M T.Fr (gen T zV) h₁ EC MC
    hgen hsm

  have hσ' : ∀ a, ValAt Or.𝔐.ξ (gen T zV) (Or.𝔐.emb s a) (algebraMap T.V T.Fr (σ a)) := fun a =>
    TopFibre.valAt_comp (algebraMap T.V T.Fr) (hσ a) h₁
  have P0 : Or.𝔐.M.ValAt (gen T zV) 0 (MC.pt 0) :=
    (hev1 _ _).2 ⟨zero_mem _, map_zero ev'⟩
  have P1 : ∀ (a : 𝓞 E) {e w}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (Or.𝔐.ρ a e) (MC.pt (ρC a w)) := fun a e w h => by
    haveI := Or.𝔐.t.act.hom a
    have h1 := Flat.CPoint.valAt_of_isDiffOf (Or.𝔐.t.act.act a) (Or.𝔐.ρ a) (Or.𝔐.act a) h
    rwa [← hact a w] at h1
  have P2 : ∀ {a : RM.Ω} {r : T.Fr} {e w}, ValAt Or.𝔐.ξ (gen T zV) a r → Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (a • e) (MC.pt (r • w)) := fun {a r e w} ha h => by
    obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
    have ha' : a ∈ regAt Or.𝔐.ξ ⟨centre (gen T zV), h₁⟩ := by
      obtain ⟨_, s', e1, -⟩ := ha
      exact ⟨s', e1⟩
    exact (hev1 _ _).2 ⟨(Or.𝔐.M.lat _).smul_mem ⟨a, ha'⟩ he, hev2 ⟨a, ha'⟩ r ⟨e, he⟩ ha⟩
  have P3 : ∀ {e e' w w'}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) → Or.𝔐.M.ValAt (gen T zV) e' (MC.pt w') →
      Or.𝔐.M.ValAt (gen T zV) (e + e') (MC.pt (w + w')) := fun {e e' w w'} h h' => by
    obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
    obtain ⟨he', rfl⟩ := (hev1 _ _).1 h'
    exact (hev1 _ _).2 ⟨add_mem he he', map_add ev' ⟨e, he⟩ ⟨e', he'⟩⟩
  have Pu : ∀ {e w w'}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) → Or.𝔐.M.ValAt (gen T zV) e (MC.pt w') → w = w' :=
    fun {e w w'} h h' => by
      obtain ⟨he, rfl⟩ := (hev1 _ _).1 h
      obtain ⟨he', rfl⟩ := (hev1 _ _).1 h'
      rfl
  obtain ⟨n, a, b, hop⟩ := GlobalTheory.CompanionTheory.Ar.Sandwich.Sep.exists_eigen_op_discr E

  let Tc : EC →ₗ[T.Fr] EC := ∑ i, algebraMap T.V T.Fr (σ (b i)) • ρC (a i)
  have hTc : ∀ w, Tc w = ∑ i, ((algebraMap T.V T.Fr).comp σ) (b i) • ρC (a i) w := fun w => by
    simp [Tc, LinearMap.sum_apply]
  have Pt : ∀ {e w}, Or.𝔐.M.ValAt (gen T zV) e (MC.pt w) →
      Or.𝔐.M.ValAt (gen T zV) (∑ i, Or.𝔐.emb s (b i) • Or.𝔐.ρ (a i) e) (MC.pt (Tc w)) := fun {e w} h => by
    rw [hTc]
    have : ∀ S : Finset (Fin n), Or.𝔐.M.ValAt (gen T zV) (∑ i ∈ S, Or.𝔐.emb s (b i) • Or.𝔐.ρ (a i) e)
        (MC.pt (∑ i ∈ S, ((algebraMap T.V T.Fr).comp σ) (b i) • ρC (a i) w)) := fun S => by
      classical
      induction S using Finset.induction_on with
      | empty => simpa using P0
      | insert i S hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi]
        exact P3 (P2 (hσ' _) (P1 _ h)) ih
    exact this _
  have hD : IsUnit ((discr E : ℤ) : T.V) :=
    isUnit_int_of_inFibre_rf (ξ := Or.𝔐.ξ) zV h₀ hp hF hdisc
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro w ⟨h, e', he, hw⟩
    have he' : e' ∈ Or.𝔐.dR s ⟨centre zV, h₀⟩ := hV ▸ he
    refine ⟨Submodule.subset_span ⟨h, e', he'.1, hw⟩, ?_⟩
    have heig : ∀ x, Or.𝔐.ρ x e' = Or.𝔐.emb s x • e' := fun x => by
      have := (Submodule.mem_iInf _).1 he'.2 x
      simpa [sub_eq_zero] using this
    refine (Submodule.mem_iInf _).2 fun x => ?_
    have h1 := P1 x hw
    rw [heig x] at h1
    have h2 := Pu h1 (P2 (hσ' x) hw)
    simp [sub_eq_zero, h2]
  · rintro w ⟨hw1, hw2⟩
    have key : ∀ u ∈ Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC, Tc u ∈ Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC := fun u hu => by
      induction hu using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨h, e', he, hv⟩ := hu
        refine Submodule.subset_span ⟨h, _, ?_, Pt hv⟩
        show _ ∈ Or.𝔐.V s ⟨centre zV, h₀⟩
        rw [hV]
        refine ⟨Submodule.sum_mem _ fun i _ => ?_, (hop RM.Ω Or.𝔐.Li Or.𝔐.ρ (Or.𝔐.emb s)).1 e'⟩
        have hreg : Or.𝔐.emb s (b i) ∈ regAt Or.𝔐.ξ ⟨centre zV, h₀⟩ := by
          obtain ⟨_, s', e1, -⟩ := hσ (b i)
          exact ⟨s', e1⟩
        exact (Or.𝔐.M.lat _).smul_mem ⟨_, hreg⟩ (lat_act_of_model_rf Or.𝔐 _ _ _ he)
      | zero => simp
      | add u v _ _ hu hv =>
        rw [map_add (f := _)]
        exact add_mem hu hv
      | smul r u _ hu =>
        rw [LinearMap.map_smul_of_tower]
        exact Submodule.smul_mem _ r hu
    have hT : Tc w = ((discr E : ℤ) : T.Fr) • w := by
      rw [hTc]
      exact (hop T.Fr EC ρC ((algebraMap T.V T.Fr).comp σ)).2 w hw2
    obtain ⟨u, hu⟩ := hD.exists_left_inv
    have e1 : w = u • Tc w := by
      rw [hT, ← map_intCast (algebraMap T.V T.Fr), algebraMap_smul, smul_smul, hu, one_smul]
    rw [e1]
    exact Submodule.smul_mem _ u (key w hw1)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.PositivityTheory.UnitarySelfGeneration.root_origin_frame_comparison : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → p ∉ SS → ¬ (p : ℤ) ∣ discr E → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (σ : 𝓞 E →+* T.V), (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → Or.𝔐.M.fibAt (Or.𝔐.V s) zV MC = FinRd.Roots.lieEig Or MC ρC σ := by
  exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.fib_eq_lieEig_rf

end
end
end

-- bundled from Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ValFFromSpecStalk
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Points GlobalTheory.Cartier GlobalTheory.ZH

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination

theorem valF_fromSpecStalk (X : Scheme.{0}) [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)) :
    valF (F := X.functionField) (X.fromSpecStalk (genericPoint X)) U f = fnOf U h f := by
  have hsp : ∀ w, (X.fromSpecStalk (genericPoint X)).base w ⤳ genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact hw
  have hU : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
    intro w _
    exact (hsp w).mem_open U.isOpen h
  have key : Scheme.Hom.appLE (X.fromSpecStalk (genericPoint X)) U ⊤ hU ≫
      (Scheme.ΓSpecIso (X.presheaf.stalk (genericPoint X))).hom = X.presheaf.germ U (genericPoint X) h := by
    rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app h]
    simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl, op_id,
      Functor.map_id, Category.id_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.comp_id]
    simp
  unfold valF
  rw [dite_eq_left hU]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ f) key

private theorem top_le_map_fromSpecStalk_genericPoint (X : Scheme.{0}) [IsIntegral X] (U : X.Opens)
    (h : genericPoint X ∈ U) : ⊤ ≤ (Opens.map (X.fromSpecStalk (genericPoint X)).base).obj U := by
  intro w _
  have hw : (X.fromSpecStalk (genericPoint X)).base w ∈ Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨w, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hw
  exact hw.mem_open U.isOpen h

private theorem valF_spMap_comp' {K L : Type} [Field K] [Field L] (σ : K →+* L) {Y : Scheme.{0}}
    (y : Sp K ⟶ Y) (U : Y.Opens) (hy : ⊤ ≤ (Opens.map y.base).obj U) (f : Γ(Y, U)) :
    valF (spMap σ ≫ y) U f = σ (valF y U f) := by
  have h2 : ⊤ ≤ (Opens.map (spMap σ ≫ y).base).obj U := fun w _ => hy (Opens.mem_top ((spMap σ).base w))
  have k2 : Scheme.Hom.appLE (spMap σ) ⊤ ⊤ (fun _ _ => trivial) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom =
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom ≫ CommRingCat.ofHom σ := by
    have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
    convert hn using 2
    exact Scheme.Hom.appLE_eq_app (spMap σ) (U := ⊤)
  unfold valF
  rw [dite_eq_left h2, dite_eq_left hy, ← Scheme.Hom.appLE_comp_appLE (spMap σ) y U ⊤ ⊤ hy (fun _ _ => trivial)]
  exact congrArg (fun φ => CommRingCat.Hom.hom φ (CommRingCat.Hom.hom (Scheme.Hom.appLE y U ⊤ hy) f)) k2

theorem exists_pt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp o)
    (ψ : Ω →+* X.functionField) (hψ : Function.Bijective ψ)
    (hb : ∀ a : o, ψ (algebraMap o Ω a) = fnOf ⊤ (Opens.mem_top _) (algX p ⊤ a)) :
    ∃ pt : Sp Ω ⟶ X, pt ≫ p = spMap (algebraMap o Ω) ∧ Set.range pt = {genericPoint X} ∧
      (∀ x : Ω, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)), ψ (valF pt U f) = fnOf U h f := by
  let e : Ω ≃+* X.functionField := RingEquiv.ofBijective ψ hψ
  let σ : X.functionField →+* Ω := e.symm.toRingHom
  have H4 : ∀ (U : X.Opens) (h : genericPoint X ∈ U) (f : Γ(X, U)),
      ψ (valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) U f) = fnOf U h f := by
    intro U h f
    rw [valF_spMap_comp' σ _ U (top_le_map_fromSpecStalk_genericPoint X U h) f, valF_fromSpecStalk X U h f]
    exact e.apply_symm_apply _
  have hval : ∀ a : o, valF (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ (algX p ⊤ a) = algebraMap o Ω a := by
    intro a
    apply hψ.1
    rw [H4 ⊤ (Opens.mem_top _) (algX p ⊤ a), hb a]
  have hrange : ∀ w, (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base w = genericPoint X := by
    intro w
    have hw : (X.fromSpecStalk (genericPoint X)).base ((spMap σ).base w) ∈
        Set.range (X.fromSpecStalk (genericPoint X)).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hw
    exact (Specializes.antisymm hw ((genericPoint_spec ↥X).specializes trivial)).eq
  refine ⟨(spMap σ ≫ X.fromSpecStalk (genericPoint X)), ?_, ?_, ?_, H4⟩
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of o)).inv,
      ← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom]
    have hR : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ (spMap (algebraMap o Ω)).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      rw [spMap, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    have hL : (Scheme.ΓSpecIso (CommRingCat.of o)).inv ≫ ((spMap σ ≫ X.fromSpecStalk (genericPoint X)) ≫ p).appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap o Ω) := by
      ext a
      change _ = algebraMap o Ω a
      rw [← hval a]
      have q1 : Scheme.Hom.appLE p ⊤ ⊤ (fun _ _ => trivial) = p.appTop := Scheme.Hom.appLE_eq_app p (U := ⊤)
      have q2 : Scheme.Hom.appLE (spMap σ ≫ X.fromSpecStalk (genericPoint X)) ⊤ ⊤ (fun _ _ => trivial) = (spMap σ ≫ X.fromSpecStalk (genericPoint X)).appTop :=
        Scheme.Hom.appLE_eq_app _ (U := ⊤)
      unfold valF algX
      rw [dite_eq_left (show ⊤ ≤ (Opens.map (spMap σ ≫ X.fromSpecStalk (genericPoint X)).base).obj ⊤ from fun _ _ => trivial),
        q1, q2]
      rfl
    simp only [Category.assoc] at hL hR ⊢
    rw [hL, hR]
  · refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨IsLocalRing.closedPoint Ω, hrange _⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    exact hrange w
  · intro x
    obtain ⟨V, hV, s, hs⟩ := X.presheaf.exists_germ_eq (ψ x)
    refine ⟨V, s, ⟨_, hV⟩, hψ.1 ?_⟩
    rw [H4 V hV s]
    exact hs

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination
end

