module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EqZeroOfMulEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Definitions.TorusSections.ExistsSecTie
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0050
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcFramedPointUniqueAndBaseChange
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationsSymmetricFrameAndTerms
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EqZeroOfMulEqZeroOfReadingNeZero
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem eq_zero_of_mul_eq_zero_of_reading_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (a a' : (E →+* ℂ) × ℕ → ℕ) (n n' : ℕ) (f g : Rul Xo c), Dom a n → Dom a' n' → f ∈ sec Xo c a n → g ∈ sec Xo c a' n' → (∀ k, ∃ x ∈ (U.X k).dom, rdU U f k x ≠ 0) → f * g = 0 → g = 0 := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU a a' n n' f g ha ha' hf hg hne hfg
  refine (GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.firstFiveLaws.1.secBaseChange
    E H Dw l Xo c σ r U hU a' n').2 g hg fun k => ?_
  obtain ⟨x0, hx0, hx0ne⟩ := hne k
  refine ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero (FourierCoefficientDomain.isOpen_dom _)
    (GlobalTheory.frames_isConnected E r (U.X k)).isPreconnected (hU.2.2.2.2.1 a n ha f hf k).1
    (hU.2.2.2.2.1 a' n' ha' g hg k).1 (fun y hy => ?_) hx0 hx0ne
  have hmul : rdU U (f * g) k y = rdU U f k y * rdU U g k y := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hy]
    exact evalAt_mul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f g (U.un k ⟨y, hy⟩)
  have h0 : rdU U (f * g) k y = 0 := by
    rw [hfg, map_zero]
    rfl
  exact hmul.symm.trans h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaProductRuleValueEqProductFormOfTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.EtaForm


open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
set_option autoImplicit false in
theorem _root_.GlobalTheory.EtaForm.etaValAt_evR_of_fromTest : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (R : ℕ), Odd R → ∀ (J : Type) [Fintype J] (n : ℕ) (cf : J → ℤ) (xs : J → Fin n → _root_.GlobalTheory.EtaForm.LatMod Dw (R ^ 4)) (f : _root_.Formalism.L2.Pj.Rul Xo c), _root_.GlobalTheory.EtaForm.IsEtaRule Xo c R cf xs f → ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : _root_.Formalism.L2.Pj.FrPt Xo c S), _root_.Formalism.L2.Pj.FromTest (K := c.F) (fun S _ _ => _root_.Formalism.L2.Pj.FrPt Xo c S) (fun φ y z => _root_.Formalism.L2.Pj.FrMap φ y z) y → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y (_root_.Formalism.L2.Pj.evR Xo c f y) ∧ ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (φ : S →ₐ[c.F] S') (z : _root_.Formalism.L2.Pj.FrPt Xo c S'), _root_.Formalism.L2.Pj.FrMap φ y z → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs z (φ (_root_.Formalism.L2.Pj.evR Xo c f y)) := by
  intro E _ _ _ H Dw l Xo c R hR J _ n cf xs f hf S _ _ y hy
  have hlaws := _root_.GlobalTheory.EtaForm.etaValAt_existsUnique_natural _root_.GlobalTheory.firstFiveLaws.1
    E H Dw l Xo c R hR J n cf xs
  have transport : ∀ (S₀ S₁ : Type) [CommRing S₀] [Algebra c.F S₀] [CommRing S₁] [Algebra c.F S₁]
      (φ : S₀ →ₐ[c.F] S₁) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c S₀) (y₁ : _root_.Formalism.L2.Pj.FrPt Xo c S₁) (v : S₀),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y₁ → _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ v →
        _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₁ (φ v) := by
    intro S₀ S₁ _ _ _ _ φ y₀ y₁ v hφ hv
    obtain ⟨w, hw, -⟩ := hlaws.1 S₁ y₁
    rwa [hlaws.2 S₀ S₁ φ y₀ y₁ hφ v w hv hw]
  have key : ∃ (p : _root_.Formalism.L2.Pj.TRing c.F) (φ : p.R →ₐ[c.F] S) (y₀ : _root_.Formalism.L2.Pj.FrPt Xo c p.R),
      _root_.Formalism.L2.Pj.FrMap φ y₀ y ∧ _root_.Formalism.L2.Pj.evR Xo c f y = φ (f p y₀) := by
    refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
      hy.choose_spec.choose_spec.choose_spec, ?_⟩
    unfold _root_.Formalism.L2.Pj.evR _root_.Formalism.L2.Pj.evalAt
    rw [dite_eq_left hy]
  obtain ⟨p, φ, y₀, hφ, hval⟩ := key
  have h₀ : _root_.GlobalTheory.EtaForm.EtaValAt Xo c R cf xs y₀ (f p y₀) := hf p y₀
  refine ⟨hval ▸ transport _ _ φ y₀ y _ hφ h₀, ?_⟩
  intro S' _ _ ψ z hz
  rw [hval]
  exact transport _ _ (ψ.comp φ) y₀ z _ (_root_.GlobalTheory.FramedBaseChange.trans φ ψ hφ hz) h₀

end GlobalTheory.EtaForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsHeisenbergLiftsSpanLatticeClasses
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal

theorem exists_qkPt_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V] [IsAdicComplete (maximalIdeal V) V] (G : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) G), P.TorsionIso → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (ev : M → (TFK (R := V) F ⟶ P.A.A)), (∀ a b, ev (a + b) = ev a * ev b) → (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ (letI := H.starRing; P.oA.act o : P.A.A ⟶ P.A.A)) → (∀ a, ev a ^ N = 1) → (∀ u, u ^ N = 1 → ∃ a, ev a = u) → ∃ pt : M → QkPt P.D.toPre F N, (∀ a, P.ToA F N (pt a) (ev a)) ∧ ∀ (n : ℕ) (z : Fin n → M), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ a : P.D.toPre.X, ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, a = u + N • t := by
  intro E _ _ _ H V _ _ _ _ hc G P hT F _ _ _ N hN M _ _ ev hadd hsm hpow hsurj
  letI := H.starRing
  open GlobalTheory.TorusExt in
  obtain ⟨f, hto, hon, heq, hfa, hfs, -⟩ := hT F N hN
  have hB := P.D.tau_bimult
  have hG : GlobalFnsSt := GlobalTheory.SemiRigid.globalFns
  letI := GlobalTheory.TorusExt.gtGroup P.D.toPre F
  let iotaLocal : P.D.toPre.X →+ GtPtF P.D.toPre F := AddMonoidHom.mk'
    (fun x => (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose) (by
      intro x x'
      obtain ⟨b, v⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x).choose_spec
      obtain ⟨b', v'⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB x').choose_spec
      obtain ⟨b'', v''⟩ := (GlobalTheory.TorusExt.isIota_iff_val _ _).1 (GlobalTheory.TorusExt.exists_iota (F := F) hB (x + x')).choose_spec
      refine (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 ((GlobalTheory.TorusExt.isAdd_iff_val _ _ _).2 ⟨by rw [b, b', b'', cPoint_add], fun χ y J hJ => ?_⟩)
      have sym01 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J b a c := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_first (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      have sym12 (a b c : TF (R := V) F ⟶ P.D.toPre.P.A) :
          th P.D.toPre y J a b c = th P.D.toPre y J a c b := by
        have e := (val_corr hJ P.D.toPre.cub.cubeSymmetric_swap_last (lift a (lift b c)).left).trans
          (val_cub P.D.toPre.cub (lift a (lift b c)) hJ _ _ _)
        refine e.trans ?_
        congr 1 <;> simp [x3]
      rw [v χ y J hJ, v' χ y J hJ, v'' χ y J hJ, b, b', sym01, sym12]
      exact tau_mul (𝟙 (TF (R := V) F)) hJ hB x x' χ)
  have hi (x : P.D.toPre.X) : GtPtF.IsIota x (iotaLocal x) := (GlobalTheory.TorusExt.exists_iota hB x).choose_spec
  have hn (p : QkPt P.D.toPre F N) : N • p.g = iotaLocal p.y := by
    obtain ⟨h, hn, hi'⟩ := p.eq
    exact ((GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 hn).symm.trans (GlobalTheory.TorusExt.isIota_unique hi' (hi p.y))
  choose pt hpt using fun a => hon (ev a) (hpow a)
  refine ⟨pt, fun a => (hto _ _).2 (hpt a).symm, fun n z hz y => ?_⟩
  have yadd : ∀ a b, ∃ t : P.D.toPre.X, (pt (a + b)).y = (pt a).y + (pt b).y + N • t := fun a b => by
    let q : QkPt P.D.toPre F N := ⟨(pt a).y + (pt b).y, (pt a).g + (pt b).g,
      iotaLocal ((pt a).y + (pt b).y), (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 (by
        rw [nsmul_add, hn, hn, map_add]), hi _⟩
    have e := hfa _ _ _ (show QkAdd (pt a) (pt b) q from
      ⟨q, rfl, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl, qk_equiv_refl hB q⟩)
    rw [hpt, hpt, ← hadd, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, ht⟩
  have ysm : ∀ (o : 𝓞 E) a, ∃ t : P.D.toPre.X, (pt (o • a)).y = o • (pt a).y + N • t := fun o a => by
    obtain ⟨q, hq⟩ := qkAct_exists hG hB P.oD o (pt a)
    obtain ⟨r, hr, hact, he⟩ := hq
    have e := hfs _ _ _ (show QkAct P.oD o (pt a) r from ⟨r, hr, hact, qk_equiv_refl hB r⟩)
    rw [hpt, ← hsm, ← hpt] at e
    obtain ⟨t, ht, -⟩ := (heq _ _).1 e
    exact ⟨t, by simpa [hr] using ht⟩
  have key : ∀ m ∈ Submodule.span (𝓞 E) (Set.range z),
      ∃ u ∈ Submodule.span (𝓞 E) (Set.range fun b => (pt (z b)).y), ∃ t : P.D.toPre.X, (pt m).y = u + N • t := by
    intro m hm
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      exact ⟨_, Submodule.subset_span ⟨b, rfl⟩, 0, by rw [smul_zero, add_zero]⟩
    | zero =>
      obtain ⟨t, ht⟩ := ysm 0 0
      rw [zero_smul, zero_smul] at ht
      exact ⟨0, Submodule.zero_mem _, t, ht⟩
    | add a b _ _ ha hb =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨u', hu', t', ht'⟩ := hb
      obtain ⟨s, hs⟩ := yadd a b
      exact ⟨u + u', Submodule.add_mem _ hu hu', t + t' + s, by
        rw [hs, ht, ht', smul_add, smul_add]; abel⟩
    | smul o a _ ha =>
      obtain ⟨u, hu, t, ht⟩ := ha
      obtain ⟨s, hs⟩ := ysm o a
      exact ⟨o • u, Submodule.smul_mem _ o hu, o • t + s, by
        rw [hs, ht, smul_add, smul_add, smul_comm o N t, add_assoc]⟩
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨g, hg⟩ := (GlobalTheory.UT.gt_onto_divisible_kernel GlobalTheory.firstFiveLaws V _ hA P.D F).2.1 N hN
    (iotaLocal y)
  let p : QkPt P.D.toPre F N :=
    ⟨y, g, iotaLocal y, hg, hi y⟩
  have hp : f p ^ N = 1 := by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((hto p _).2 rfl w hw).1
  obtain ⟨m, hm⟩ := hsurj _ hp
  obtain ⟨s, hs, -⟩ := (heq (pt m) p).1 ((hpt m).trans hm)
  obtain ⟨u, hu, t, ht⟩ := key m (hz ▸ Submodule.mem_top)
  refine ⟨u, hu, t + s, ?_⟩
  have hs' : y = (pt m).y + N • s := hs
  rw [hs', ht, smul_add, add_assoc]

end GlobalTheory.EtaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.FullLinearLevelEqExpPeriodsComplexPoint
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LevelPeriods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem exists_periods (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ))
    (hP : IsPeriod (Fu.Di i) ty Pm) (N : ℕ) (hN : 0 < N)
    (ev : LatMod Dw N → (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G)) (hev : IsFullLev Xo N (Fu.u i Pm) ev) :
    ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, ev q = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q)) ∧ ev q ^ N = 1) ∧
      ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La,
        ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  let f : (Fin g → ℂ) →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (Fu.ex i Pm z)) fun z w => congrArg Additive.ofMul (Fu.ex_add i Pm hP z w)
  let e : LatMod Dw N →+ Additive (ptO Xo (Fu.u i Pm) ⟶ Xo.univ.t.G) :=
    AddMonoidHom.mk' (fun q => Additive.ofMul (ev q)) fun a b => congrArg Additive.ofMul (hev.1 a b)
  have hker : ∀ z, f z = 0 ↔ z ∈ Pm.range := fun z => Fu.ex_ker i Pm hP z
  have hNN : ∀ z : Fin g → ℂ, N • ((N : ℂ)⁻¹ • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  have hNN' : ∀ z : Fin g → ℂ, (N : ℂ)⁻¹ • (N • z) = z := fun z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  have hpow : ∀ q, ev q ^ N = 1 := FullLevel.pow_eq_one Xo hev
  have hex : ∀ q, ∃ a, e q = f ((N : ℂ)⁻¹ • Pm a) := fun q => by
    obtain ⟨z, hz⟩ := Fu.ex_onto i Pm hP (ev q)
    have hz' : f z = e q := congrArg Additive.ofMul hz
    have h0 : N • e q = 0 := congrArg Additive.ofMul (hpow q)
    rw [← hz', ← map_nsmul, hker] at h0
    obtain ⟨a, ha⟩ := h0
    exact ⟨a, by rw [ha, hNN', hz']⟩
  choose a ha using hex
  refine ⟨a, fun q => ⟨congrArg Additive.toMul (ha q), hpow q⟩, fun n z hz u => ?_⟩
  have hu : N • f ((N : ℂ)⁻¹ • Pm u) = 0 := by
    rw [← map_nsmul, hNN, hker]
    exact ⟨u, rfl⟩
  obtain ⟨q, hq⟩ := FullLevel.onto_of_local Xo GlobalTheory.firstFiveLaws.1 hN hev (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm u))
    (congrArg Additive.toMul hu)
  have hq' : e q = f ((N : ℂ)⁻¹ • Pm u) := congrArg Additive.ofMul hq
  obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 (hz ▸ Submodule.mem_top : q ∈ Submodule.span (𝓞 E) (Set.range z))
  have hlin : ∀ (o : 𝓞 E) r, e (o • r) = f ((N : ℂ)⁻¹ • Pm (o • a r)) := fun o r => by
    have h1 : (N : ℂ)⁻¹ • Pm (o • a r) = fun k => ty k (o : E) * ((N : ℂ)⁻¹ • Pm (a r)) k := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul, hP.1]
      ring
    have h2 : ev r = Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a r)) := congrArg Additive.toMul (ha r)
    refine congrArg Additive.ofMul (?_ : ev (o • r) = Fu.ex i Pm _)
    rw [h1, Fu.ex_lin i Pm hP, hev.2.1, h2]
  have hsum : e q = f ((N : ℂ)⁻¹ • Pm (∑ b, cf b • a (z b))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hcf, map_sum, map_sum, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun b _ => hlin _ _
  have h0 : f ((N : ℂ)⁻¹ • Pm (u - ∑ b, cf b • a (z b))) = 0 := by
    rw [map_sub, smul_sub, map_sub, ← hq', ← hsum, sub_self]
  obtain ⟨v, hv⟩ := (hker _).1 h0
  refine ⟨cf, v, ?_⟩
  have h1 : N • v = u - ∑ b, cf b • a (z b) := hP.2.1 (by rw [map_nsmul, hv, hNN])
  rw [h1, add_sub_cancel]

end LevelPeriods

theorem fullLevel_eq_exp_periods :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (y : FrPt Xo c (CAt σ)), IsPeriod (Fu.Di i) ty Pm → y.x = Fu.u i Pm → ∀ (N : ℕ), 0 < N → ∀ ev : LatMod Dw N → (ptO Xo y.x ⟶ Xo.univ.t.G), IsFullLev Xo N y.x ev → ∃ a : LatMod Dw N → (Fu.Di i).La, (∀ q, (ev q).left = (Fu.ex i Pm ((N : ℂ)⁻¹ • Pm (a q))).left ∧ ev q ^ N = 1) ∧ ∀ (n : ℕ) (z : Fin n → LatMod Dw N), Submodule.span (𝓞 E) (Set.range z) = ⊤ → ∀ u : (Fu.Di i).La, ∃ (cf : Fin n → 𝓞 E) (v : (Fu.Di i).La), u = ∑ b, cf b • a (z b) + N • v := by
  intro E _ _ _ H Dw l Xo c σ g ty Fu i Pm y hP hy N hN ev hev
  obtain ⟨x, _, _, _, _, _, _, _⟩ := y
  dsimp only at hy ev hev ⊢
  subst hy
  obtain ⟨a, h1, h2⟩ := LevelPeriods.exists_periods Fu i Pm hP N hN ev hev
  exact ⟨a, fun q => ⟨congrArg CommaMorphism.left (h1 q).1, (h1 q).2⟩, h2⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.IntegralThetaSectionExistsAndBaseChange
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaVal


open GlobalTheory.ArcQ GlobalTheory.Frames GlobalTheory.Reg.ChartInhab GlobalTheory.Reg.LiftUnique in
theorem intSec_baseChange {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V')
    (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V'))
    (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (m : SABMap G' G (spMap φ)) (I : IntSec Xo V y.x y.s G)
    (hψ : ∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) (hm : FrMap ψ y y') :
    Nonempty (IntSec Xo V' y'.x y'.s G') := by
  obtain ⟨t, m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := I
  obtain ⟨hx, -, pm, hs, hf, ha⟩ := hm
  obtain ⟨t', ⟨n⟩⟩ : ∃ t' : SAB H (Sp (FractionRing V')), Nonempty (SABMap t' t (spMap ψ.toRingHom)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap ψ.toRingHom) t
    exact ⟨_, ⟨m⟩⟩
  have hι : ψ.toRingHom.comp (algebraMap V (FractionRing V)) = (algebraMap V' (FractionRing V')).comp φ :=
    RingHom.ext hψ
  have hio : spMap (algebraMap V' (FractionRing V')) ≫ spMap φ =
      spMap ψ.toRingHom ≫ spMap (algebraMap V (FractionRing V)) := by
    rw [← FrBC.spMap_comp', ← FrBC.spMap_comp', hι]
  obtain ⟨w0, r0⟩ := exists_rigIso n
  obtain ⟨m1', e₁, -⟩ := exists_comp_rig m1 n y'.x hx a1 r0
  obtain ⟨m2', e₂, -⟩ := exists_comp_rig m2 n _ hio a2 r0
  have T₀ := (FrUniq.tie_iff m1 m2 θ y.s).1 ⟨w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩
  have T₁ := FrUniq.tie_pull m1 m2 θ y.s n m1' m2' hx hio e₁ e₂ y'.s pm hs hf (fun Z r z j hz => by
    have hle := FramedBaseChange.chart_le pm hs (fun _ => j)
    rw [← ha _ hle, gs_appLE pm _ _ hle r z hz]) T₀
  obtain ⟨w1', w2', σ', s1', θ2', r1, r2, i1, i2, p2, hg⟩ := (FrUniq.tie_iff m1' m2' θ y'.s).2 T₁
  obtain ⟨m', e₃⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m m2'
  obtain ⟨w, θ', rw', iw⟩ := pull_sec G G' m θ
  have pw : PullSec m.φ θ (thfPull G.PP.L m.φ θ) := fun _ _ => rfl
  obtain ⟨w', r', i'⟩ := FrBC.exists_isoMaps_cancel m m' m2' rfl e₃ rw' r2 iw pw i2 p2
  exact ⟨⟨t', m1', m', θ', w1', w', σ', s1', _, r1, r', i1, i', fun _ _ => rfl, hg⟩⟩

theorem intSec_exists_and_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), (∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), letI := io.toAlgebra; ∃ G : SAB H (Sp T.V), Nonempty (IntSec Xo T.V y.1.x y.1.s G)) ∧ ∀ (V V' : Type) [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V'] [Algebra c.F (FractionRing V)] [Algebra c.F (FractionRing V')] (φ : V →+* V') (ψ : FractionRing V →ₐ[c.F] FractionRing V') (y : FrPt Xo c (FractionRing V)) (y' : FrPt Xo c (FractionRing V')) (G : SAB H (Sp V)) (G' : SAB H (Sp V')) (_ : SABMap G' G (spMap φ)) (_ : IntSec Xo V y.x y.s G), (∀ a, ψ (algebraMap V _ a) = algebraMap V' _ (φ a)) → FrMap ψ y y' → Nonempty (IntSec Xo V' y'.x y'.s G') := by
  intro E _ _ _ H Dw l Xo c
  refine ⟨fun T io y => ?_, fun V V' _ _ _ _ _ _ φ ψ y y' G G' m I hψ hm =>
    intSec_baseChange φ ψ y y' G G' m I hψ hm⟩
  obtain ⟨G, t', m1, m2, -, θ, -, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩ := y.2.2
  exact ⟨G, ⟨⟨t', m1, m2, θ, w1, w2, σ, s1, θ2, a1, a2, a3, a4, a5, a6⟩⟩⟩

end GlobalTheory.EtaVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LeValuationOddLevelThetaConstantIntegralExpansio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj GlobalTheory.EtaForm GlobalTheory.EtaVal
open Formalism.MainNotions.DIV.Cons (SCF intO)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.EtaVal
open GlobalTheory.UT GlobalTheory.TorusExt GlobalTheory.UT.ThetaConstVal

attribute [local instance] gtGroup

theorem le_val_thetaConst : GlobalTheory.UT.AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, GlobalTheory.UT.NormW U.toUnifPre w₀ ρ → ∀ (th : GlobalTheory.UT.SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → NuGe D Q F v 1 ϑ 0 → ∀ (m : ℕ), Odd m → ∀ (p : QkPt D.toPre F (m ^ 2)) x t c, QkToAkU U.toUnifPre F (m ^ 2) p x → GlobalTheory.UT.ThC A ρ m th x t c → ∀ q : ℚ, (∀ χ, q ≤ (Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ)) → (q : WithTop ℚ) ≤ v c := by
  obtain ⟨hL, h₁, h₂, h₃, h₄⟩ := GlobalTheory.lawsAndExpansions
  intro V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP m hm p x t c hx hT q hq
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨w, hw⟩ := (GlobalTheory.UT.SymFrame.main hL V _ hA D F (m ^ 2) hm.pow p).1
  obtain ⟨κ, hκ⟩ := exists_kap D.toPre hL.1.mulPull m
  obtain ⟨w', hw', e⟩ := exists_frm D.toPre m p.g.b (m • p.g).b (nsmul_b m p.g) w hw.1 κ hκ.1
  have hg : GtPtF.IsNsmul m p.g (m • p.g) := (isNsmul_iff_eq _ _ _).2 rfl
  have s := (GlobalTheory.UT.ThetaSum.theta_const_sum hL V _ hA D A G hG U F w₀ ρ hN th ϑ hE m hm p x t c hx hT w hw _ hg κ hκ w' hw' e).1
  obtain ⟨-, -, a⟩ := (GlobalTheory.UT.TxVal.main hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv).2 m hm.pos p w hw _ hg κ hκ w' hw' e
  exact le_of_sumV (AdicValSum.main V ϖ hϖ F v hv _ _ _ s).1 fun χ =>
    (WithTop.coe_le_coe.2 (hq χ)).trans (a ϑ hP χ)

end GlobalTheory.EtaVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogCardComponentsLeOfRowsBound
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem log_card_comp_le_of_rows : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * zBase large₂ ^ 2 := by
  intro D T h large₂ ⟨h2, hrL, hrd, hf, hg, h16⟩ j hj σ hσ
  obtain ⟨ξ, AA, hsk, hne, hFG, hA, hdual⟩ := PerfectTrace.exists_perfect_trace_ideal D
  obtain ⟨-, -, hM, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hfd : FD.fdeg D.host.E = D.R.f := by
    unfold FD.fdeg; rw [hfin]; omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hdE : Real.log (FD.dE D.host.E) ≤ 4 * FD.fdeg D.host.E * large₂.sc.L := by
    unfold Formalism.BasicNotions.Host.rdE at hrd
    rw [Real.log_rpow hdisc, hfin, one_div_mul_eq_div, div_le_iff₀ (by push_cast; positivity)] at hrd
    push_cast at hrd
    rw [hfd]
    unfold FD.dE
    linarith
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.QNorm.hasseNormSt GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
    D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    ξ AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact h16) h2 hdE hrL
    (by rw [hfd]; exact hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.EtaAn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NonemptyComponentComplexUniformisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem nonempty_comp_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → 1 ≤ r → Nonempty U.Comp := by
  intro E _ _ _ H Dw l Xo c σ r U _ hU hr
  obtain ⟨y⟩ := GlobalTheory.nonempty_frPt_complex GlobalTheory.closing_of_abelianSchemeLaws
    GlobalTheory.firstFiveLaws.2.1.secTwist E H Dw l Xo c (hU.1 ▸ hr) σ
  obtain ⟨k, -⟩ := hU.2.2.1 y
  exact ⟨k⟩

end GlobalTheory
end

