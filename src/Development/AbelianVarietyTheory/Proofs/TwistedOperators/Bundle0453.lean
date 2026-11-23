module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyIrreducibleComponentsWeberValuesStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatePlacesProductIdealProperOddCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftIdeal

def conjO (D : D7) : 𝓞 D.host.E ≃+* 𝓞 D.host.E :=
  RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E).toRingEquiv

theorem coe_conjO (D : D7) (x : 𝓞 D.host.E) :
    ((conjO D x : 𝓞 D.host.E) : D.host.E) = IsCMField.complexConj D.host.E (x : D.host.E) := rfl

theorem conjO_conjO (D : D7) (x : 𝓞 D.host.E) : conjO D (conjO D x) = x := by
  apply RingOfIntegers.ext
  rw [coe_conjO, coe_conjO]
  simp

theorem star_eq (D : D7) (x : D.host.E) : star x = IsCMField.complexConj D.host.E x := rfl

theorem conjI_eq_map (D : D7) (I : Ideal (𝓞 D.host.E)) :
    conjI I = I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨b, hb, RingOfIntegers.ext ?_⟩
    rw [h]
    rfl
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, rfl⟩

theorem map_map_conjO (D : D7) (I : Ideal (𝓞 D.host.E)) :
    (I.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = I := by
  rw [Ideal.map_map]
  have : ((conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).comp (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) = RingHom.id _ :=
    RingHom.ext fun x => conjO_conjO D x
  rw [this, Ideal.map_id]

end GlobalTheory.LiftIdeal

end

noncomputable section

namespace GlobalTheory.LiftIdeal

open GlobalTheory.LiftLevel

theorem isMaximal_map (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) :
    (PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)).IsMaximal := by
  haveI := PP.isMaximal
  exact Ideal.map_isMaximal_of_equiv (conjO D)

theorem liftI_eq (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    liftI Pg Q = ∏ PP ∈ Pg ∪ Q, PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
  unfold liftI
  exact Finset.prod_congr rfl fun PP _ => conjI_eq_map D _

theorem conjI_liftI (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) :
    conjI (liftI Pg Q) = ∏ PP ∈ Pg ∪ Q, PP.asIdeal := by
  rw [conjI_eq_map, liftI_eq]
  have := map_prod (Ideal.mapHom (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E))
    (fun PP : Formalism.L2.DIV.Pl D.host.E => PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (Pg ∪ Q)
  simp only [Ideal.mapHom_apply] at this
  rw [this]
  exact Finset.prod_congr rfl fun PP _ => map_map_conjO D _

theorem map_ne {D : D7} {e : AE D} {S : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e S)
    {PP PP' : Formalism.L2.DIV.Pl D.host.E} (hP : PP ∈ S) (hP' : PP' ∈ S) :
    PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) ≠ PP'.asIdeal := by
  intro h
  refine GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP' fun c hc => ?_
  refine ⟨conjO D c, h ▸ Ideal.mem_map_of_mem _ hc, ?_⟩
  rw [coe_conjO, star_eq]

theorem liftI_props : ∀ (D : D7) (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), Pg.Nonempty →
    (∀ PP, PP ∈ Pg ∨ PP ∈ Q → (2 : 𝓞 D.host.E) ∉ PP.asIdeal) → IsIdemSum e (Pg ∪ Q) →
    GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊤ ∧ GlobalTheory.LiftLevel.liftI Pg Q ≠ ⊥ ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (conjI (GlobalTheory.LiftLevel.liftI Pg Q)) ∧
      IsCoprime (GlobalTheory.LiftLevel.liftI Pg Q) (Ideal.span {2}) := by
  intro D Pg Q e hne h2 he
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P0, hP0⟩ := hne
    intro htop
    have hle : liftI Pg Q ≤ P0.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [liftI_eq]
      exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_union_left _ hP0))
    rw [htop] at hle
    exact (isMaximal_map D P0).ne_top (top_le_iff.1 hle)
  · rw [liftI_eq, ← Ideal.zero_eq_bot]
    refine Finset.prod_ne_zero_iff.2 fun PP _ => ?_
    rw [Ne, Ideal.zero_eq_bot,
      Ideal.map_eq_bot_iff_of_injective (f := (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E)) (conjO D).injective]
    exact PP.ne_bot
  · rw [conjI_liftI, liftI_eq]
    refine IsCoprime.prod_left fun PP hP => IsCoprime.prod_right fun PP' hP' => ?_
    exact Ideal.isCoprime_iff_sup_eq.2
      ((isMaximal_map D PP).coprime_of_ne PP'.isMaximal (map_ne he hP hP'))
  · rw [liftI_eq]
    refine IsCoprime.prod_left fun PP hP => Ideal.isCoprime_iff_sup_eq.2 ?_
    have h2' : (2 : 𝓞 D.host.E) ∉ PP.asIdeal.map (conjO D : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, map_ofNat]
      exact h2 PP (Finset.mem_union.1 hP)
    exact (isMaximal_map D PP).out.2 _ (left_lt_sup.2 fun hle => h2' (hle (Ideal.mem_span_singleton_self 2)))

end GlobalTheory.LiftIdeal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

theorem coverField_of_containsRayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → QGuard R → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → GlobalTheory.TwistField.CoverField T R := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hQ hray
  unfold GlobalTheory.TwistField.CoverField
  intro i t l₂ hdvd hM hA Xo₂ c₂ hc
  obtain ⟨hHost, hLev, -, -⟩ := hT.pins
  unfold Par.PinHost at hHost
  unfold Par.PinLevel at hLev

  have hn : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t = l₂.M := by
    rw [hM, hLev.1]
    rfl

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hHost.1]
    apply Subtype.ext
    push_cast
    exact Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h3 : 3 ≤ GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t := hn ▸ l₂.three_le

  have hW := (_root_.GlobalTheory.FieldSize.WeberTransport.weberIn_of_containsRayField D.host.E T.Q.H D.host.K D.what₂.LL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) D.what₂.embLL
    (Formalism.L2.Pj.LPb.finrank_K D) hsq _ h3 (hray t)).1
  refine GlobalTheory.T.geometricallyIrreducible_components_weberValues D T.Q hT.pins ((i : ℕ) + 1) ⟨by omega, by omega⟩ l₂ Xo₂ c₂
    (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t) (by omega) ?_ (Or.inl (hc ▸ hW))
  show Nat.lcm l₂.M l₂.A ∣ _
  rw [hA, Nat.lcm_one_right, hn]

end GlobalTheory.TwistField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoversAtOverField
section
noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoverOverField

open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.Member GlobalTheory.CoverHalf Formalism.IndefR.FWT Formalism.L2.DIV GlobalTheory.TupleCover GlobalTheory.TwistField

section Roots

theorem prim_mul {L : Type} [Field L] {a b : ℕ} (hab : Nat.Coprime a b) (ha : ∃ z : L, IsPrimitiveRoot z a)
    (hb : ∃ z : L, IsPrimitiveRoot z b) : ∃ z : L, IsPrimitiveRoot z (a * b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  have h := (Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [← hx.eq_orderOf, ← hy.eq_orderOf]; exact hab)
  rw [← hx.eq_orderOf, ← hy.eq_orderOf] at h
  rw [← h]
  exact IsPrimitiveRoot.orderOf _

theorem prim_prod {L : Type} [Field L] (s : Finset ℕ) (hp : ∀ q ∈ s, q.Prime) (hz : ∀ q ∈ s, ∃ z : L, IsPrimitiveRoot z q) :
    ∃ z : L, IsPrimitiveRoot z (∏ q ∈ s, q) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine prim_mul ?_ (hz a (Finset.mem_insert_self _ _))
      (ih (fun q hq => hp q (Finset.mem_insert_of_mem hq)) (fun q hq => hz q (Finset.mem_insert_of_mem hq)))
    refine Nat.Coprime.prod_right fun q hq => ?_
    exact (Nat.coprime_primes (hp a (Finset.mem_insert_self _ _)) (hp q (Finset.mem_insert_of_mem hq))).2
      (fun h => ha (h ▸ hq))

theorem mem_range_of_pow {L : Type} [Field L] (σ : L →+* ℂ) {n : ℕ} (hn : 0 < n) (hz : ∃ z : L, IsPrimitiveRoot z n)
    {w : ℂ} (hw : w ^ n = 1) : w ∈ σ.fieldRange := by
  obtain ⟨z, hz⟩ := hz
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨i, -, hi⟩ := (hz.map_of_injective σ.injective).eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow]; exact hi⟩

end Roots

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem exists_fun_of_val {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {n r : ℕ} (d : DeltaDat Xo c n) (V : HSp D) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (hio : IotaOK Dw V ι) (hpos : 1 ≤ Dw.p + Dw.q)
    (hx₀ : ∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 →
      gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram).transpose) (x₀ τ) =
        Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ))
    (hlev : d.IsLev) (hA : d.l₂.A = 1) (hcl : FnAlgClosed (Xo := d.Xo₂) (c := d.c₂))
    (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ)
    (h1 : ∀ g : GA D V, (∃ w ∈ intAE D, ((Matrix.GeneralLinearGroup.det (finHom V g) :
      (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : Af D.host.F ⊗[D.host.F] D.host.E) - 1 = d.l₂.M • w) →
      xi (Matrix.GeneralLinearGroup.det (finHom V g)) = 1)
    (h2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (m : ℕ) (hm : 0 < m) (h3 : ∀ g : GA D V, xi (Matrix.GeneralLinearGroup.det (finHom V g)) ^ m = 1)
    (hz : ∀ g : GA D V, ((xi (Matrix.GeneralLinearGroup.det (finHom V g)) : ℂˣ) : ℂ) ∈ c.F) :
    ∃ f : Rul d.Xo₂ d.c₂, ({ d with cδ := f } : DeltaDat Xo c n).IsLev ∧ f ^ m = 1 ∧
      ∃ (U₂ : Unf d.Xo₂ d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r),
        IsUnf U₂ ∧ (∀ k, ModelW V hr (U₂.X k)) ∧
        ∃ (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ))
          (F : FamilyUnif d.Xo₂ (((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)).comp
              (IntermediateField.inclusion d.c₂.le).toRingHom)
            (fun j => relab d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) (e j).1))
          (ik : U₂.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U₂.X k).Λ)
          (th : ∀ k, (U₂.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)),
          (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictLat U₂ V hr dict₂ ι e F ik φ th x₀ ∧
          ∀ h γ : GA D V, MarkBy U₂ V hr dict₂ ι F ik φ h γ →
            rdU U₂ f (dict₂ h).1 (dict₂ h).2 =
              1 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  have hσ : d.c₂.F.val.toRingHom = (inC c).comp (d.eF.symm : d.c₂.F →+* c.F) := RingHom.ext fun _ => rfl
  have hg₂ : GoodEmb d.c₂ ((inC c).comp (d.eF.symm : d.c₂.F →+* c.F)) := by
    rw [← hσ]; rfl
  obtain ⟨C, hC, hCι, hCx⟩ := (exists_ctx D H Dw d.l₂ d.Xo₂ d.c₂ _ V r hr ι hio hpos hA hg₂).2.2 x₀ hx₀
  obtain ⟨Kf, hKf⟩ := (PrincLevel.exists_levelK_and_nhds D V d.l₂.M).1
  obtain ⟨un, dict, mu, -, -, hP⟩ := exists_pkgLaws D _ _ _ _ _ _ _ _ C hC Kf hKf 1 ⟨continuous_const, fun _ => rfl⟩
    (fun _ => rfl)
  obtain ⟨g, e, F, ik, φ, th, hth, hdu, hdl⟩ := hP.dictLaws
  obtain ⟨f, hf, hfm, -, hfx⟩ := GlobalTheory.XiFun.exists_sec_char_val D _ _ _ _ _ _ _ _ C.hr (C.unf un) dict C.ι g e F ik φ th C.x₀
    hC.iota hpos hA hg₂ hP.modelW hdl hdu.2.2.2.1 hcl xi
    (fun u _ hu => h1 u (by rw [GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers]; exact hu)) h2
    (fun h => ⟨⟨_, d.hF.symm ▸ hz h⟩, rfl⟩)
  have hfm' : f ^ m = 1 := hfm m h3
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, -, l9⟩ := hlev
  refine ⟨f, ⟨l1, l2, l3, l4, l5, l6, l7, hf, fun k _ _ _ y => ?_⟩, hfm', C.unf un, dict, hP.unf, hP.modelW,
      g, e, F, ik, φ, th, hth, ?_, fun h γ hmk => ?_⟩
  · exact GlobalTheory.XiFun.evR_ne_zero_of_pow _ _ f d.cδ m hm hfm' k y (l9 k y)
  · rw [← hCι, ← hCx]
    exact hdl
  · rw [one_mul]
    rw [← hCι] at hmk
    exact hfx h γ hmk

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem prim_tupPrime (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) :
    ∃ z : D.what₂.LL, IsPrimitiveRoot z (tupPrime R t) := by
  refine prim_prod _ (fun q hq => ?_) fun q hq => ?_
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    obtain ⟨⟨q, hq, he, -⟩, -⟩ := h PP hPP
    exact he ▸ hq
  · obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hq
    exact hr t PP (Or.inr hPP)

end Real

section Cover

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)

theorem exists_coeff_cover (t : T0) (h : Lev.IsTwistPlaces D.host.g (R.Q t)) (hr : R.fam_roots) (c' : Coeff T.Q.l)
    (hc : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) (l₂ : Level T.Q.H) (hM : l₂.M = T.Q.l.M * tupPrime R t) (hA : l₂.A = 1)
    (hcop : Nat.Coprime T.Q.l.M (tupPrime R t)) :
    ∃ c₂ : Coeff l₂, c₂.F = D.what₂.embLL.toRatAlgHom.fieldRange := by
  have hM0 : 0 < T.Q.l.M := lt_of_lt_of_le (by norm_num) T.Q.l.three_le
  have hM' : T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero hM0.ne' T.Q.l.A_pos.ne'
  have h1 : ∃ z : D.what₂.LL, IsPrimitiveRoot z T.Q.l.M := by
    have hz := c'.zeta_mem
    rw [hc] at hz
    obtain ⟨y, hy⟩ := hz
    have hp : IsPrimitiveRoot y T.Q.l.M' :=
      IsPrimitiveRoot.of_map_of_injective (f := D.what₂.embLL) (by
        have : D.what₂.embLL y = zeta T.Q.l.M' := hy
        rw [this]; exact Complex.isPrimitiveRoot_exp _ hM') D.what₂.embLL.injective
    obtain ⟨k, hk⟩ : T.Q.l.M ∣ T.Q.l.M' := Nat.dvd_lcm_left _ _
    exact ⟨y ^ k, hp.pow (Nat.pos_of_ne_zero hM') (by rw [hk, mul_comm])⟩
  have h2 := prim_mul hcop h1 (prim_tupPrime R t h hr)
  have hM2 : l₂.M' = T.Q.l.M * tupPrime R t := by simp [Level.M', hA, hM]
  have hpos : 0 < T.Q.l.M * tupPrime R t := hM ▸ lt_of_lt_of_le (by norm_num) l₂.three_le
  refine ⟨⟨c'.F, c'.fin, c'.conj, ?_, ?_⟩, hc⟩
  · rw [hc, hM2]
    exact mem_range_of_pow D.what₂.embLL hpos h2 (Complex.isPrimitiveRoot_exp _ hpos.ne').pow_eq_one
  · refine IntermediateField.adjoin_le_iff.2 ?_
    intro z hz
    rcases hz with rfl | rfl
    · exact c'.le (IntermediateField.subset_adjoin _ _ (by simp))
    · rw [hA]
      have : zeta 1 = 1 := (pow_one _).symm.trans (Complex.isPrimitiveRoot_exp 1 one_ne_zero).pow_eq_one
      rw [this]; exact c'.F.one_mem

end Cover


set_option maxHeartbeats 1000000 in
theorem coversAt_over_field (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hT : LawsJ T) (hL : R.toLevCh.Is A.μ0) (hr : R.fam_roots) (hV : XiVal R) (hC : CoverField T R) (i : Fin D.R.m) (n : ℕ)
    (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → Level T.Q.H)
    (hl : ∀ t, IsCoverLevel T.Q.l (tupPrime R t) (I t) (l₂ t)) (hH : ∀ t, HalfIs R t T.Q.l.Mb (I t))
    (c' : Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F) (hc' : c'.F = D.what₂.embLL.toRatAlgHom.fieldRange) :
    CoversAt T R i n (tupPrime R) I l₂ c' hle := by
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hpq := (exists_iotaOK D T.Q hT.pins _ hj).2
  have hpos : 1 ≤ (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q := by omega
  choose m hm ho using hL.xi_fin
  choose xi hx1 hx2 hx3 hx4 using fun t =>
    exists_xi D (Wc D i) (R.xi t) (R.xiH t) (hL.xi t) (m t) (hm t) (ho t) (hL.xi_triv t) (hL.xi_tame t)
  have hσ : GoodEmb T.Q.c (sOv T.toCore c' hle) := rfl
  obtain ⟨hio, hx₀⟩ := iotaOK_and_frame T hT _ hj _ hσ (Wc D i) (hT.spaceW _ hj _ hσ) (rank_Wc i)
  have key : ∀ t, ∃ d : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' n, d.pd = tupPrime R t ∧ d.I = I t ∧ d.l₂ = l₂ t ∧ d.IsLev ∧
      d.l₂.A = 1 ∧ FnAlgClosed (Xo := d.Xo₂) (c := d.c₂) ∧ ∃ _ : StarRing (𝓞 D.host.E), IsNab d.Xo₂ d.c₂ d.nab₂ := fun t => by
    obtain ⟨l1, l2, l3, l4, l5, l6⟩ := hl t
    obtain ⟨Xo₂⟩ := _root_.GlobalTheory.moduliScheme_levelMaps_heckePoints.1 _ _ (T.Q.Dw ((i : ℕ) + 1)) (l₂ t) hpos
    obtain ⟨c₂, hc₂⟩ := exists_coeff_cover T R t (hL.Q_pl t) hr c' hc' (l₂ t) l2 l6 l3.symm
    obtain ⟨d, a1, a2, a3, -, -, -, a4, a5⟩ := GlobalTheory.LevelCover.exists_deltaDat_isLev _ _ _ _ (T.Q.Xo ((i : ℕ) + 1)) c' hpos n
      (tupPrime R t) (I t) (l₂ t) Xo₂ c₂ (hc₂.trans hc'.symm) l1 l2 l3 l4 l5
    exact ⟨d, a1, a2, a3, a4, a3 ▸ l6, hC i t d.l₂ (a3 ▸ l1) (a3 ▸ l2) (a3 ▸ l6) _ _ (d.hF.trans hc'), a5⟩
  choose d a1 a2 a3 a4 a5 a6 a7 using key
  have hM : ∀ t, ∀ PP ∈ R.Q t, (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun t PP hPP => by
    refine (hH t).2.1 PP hPP ?_
    have h1 : (((d t).l₂.M : ℕ) : 𝓞 D.host.E) ∈ (d t).l₂.Mb :=
      Ideal.mul_le_left ((d t).l₂.prod.ge (Ideal.mem_span_singleton_self _))
    rw [(a4 t).2.2.2.1, a2] at h1
    exact Ideal.mul_le_right h1
  have hval : ∀ t (g : GA D (Wc D i)),
      ((xi t (Matrix.GeneralLinearGroup.det (finHom (Wc D i) g)) : ℂˣ) : ℂ) ∈ c'.F := fun t g => by
    obtain ⟨x, hx⟩ := (GlobalTheory.Member.isDetRoot_laws D (Wc D i)).1 g
    rw [hx1 t g x hx, hc']
    exact hV t x
  choose f b1 b2 U₂ dict₂ b3 using fun t =>
    exists_fun_of_val (d t) (Wc D i) (rank_Wc i) (iotaW T i) _ hio hpos hx₀ (a4 t) (a5 t) (a6 t) (xi t)
      (hx2 t _ (d t).l₂.odd (unrAt_of_not_mem R hL t _ (hM t))) (hx3 t) (m t) (hm t) (hx4 t) (hval t)
  refine ⟨fun t => { d t with cδ := f t }, U₂, dict₂, xi, fun t => ⟨a1 t, a2 t, a3 t⟩, fun t => ⟨b1 t, a5 t, a7 t⟩,
    fun t => ?_, hx1, ⟨1, ⟨1, one_pos, one_pow 1⟩, b3⟩, fun t => (b3 t).2.1, fun t => ⟨m t, hm t, b2 t⟩⟩
  change HalfIs R t T.Q.l.Mb (d t).I
  rw [a2]
  exact hH t

end GlobalTheory.CoverOverField

section Target
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.CoverOverField.coversAt : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → R.fam_roots → GlobalTheory.TwistField.XiVal R → GlobalTheory.TwistField.CoverField T R → ∀ (i : Fin D.R.m) (n : ℕ) (I : T0 → Ideal (𝓞 D.host.E)) (l₂ : T0 → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level T.Q.H), (∀ t, GlobalTheory.CoverHalf.IsCoverLevel T.Q.l (GlobalTheory.TwistField.tupPrime R t) (I t) (l₂ t)) → (∀ t, HalfIs R t T.Q.l.Mb (I t)) → ∀ (c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff T.Q.l) (hle : T.Q.c.F ≤ c'.F), c'.F = D.what₂.embLL.toRatAlgHom.fieldRange → GlobalTheory.TupleCover.CoversAt T R i n (GlobalTheory.TwistField.tupPrime R) I l₂ c' hle :=
  fun _ _ _ _ _ _ _ T _ R hT hL hr hV hC i n I l₂ hl hH c' hle hc' =>
    GlobalTheory.CoverOverField.coversAt_over_field T R hT hL hr hV hC i n I l₂ hl hH c' hle hc'

end Target
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesModelKFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

namespace GlobalTheory.KFinStruct

section Model

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.KFinVec

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem kFin_eq : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ = kFinSub ε σ :=
  le_antisymm (sSup_le fun W hW _ hw => ⟨W, hW.1, hw, hW.2⟩)
    fun _ ⟨W, h1, h2, h3⟩ => (le_sSup (a := W) ⟨h1, h3⟩ : W ≤ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) h2

theorem conj_lie' {A B G G' Y : Matrix (Fin n) (Fin n) ℂ} (hAB : A * B = 1) (hG : Aᴴ * G * A = G')
    (hY : Yᴴ * G + G * Y = 0) : (B * Y * A)ᴴ * G' + G' * (B * Y * A) = 0 := by
  rw [← hG]
  calc (B * Y * A)ᴴ * (Aᴴ * G * A) + Aᴴ * G * A * (B * Y * A)
      = Aᴴ * Yᴴ * (A * B)ᴴ * G * A + Aᴴ * G * (A * B) * Y * A := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Aᴴ * (Yᴴ * G + G * Y) * A := by
        rw [hAB]; simp only [conjTranspose_one, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hY]; simp

theorem exp_smul_conj' {Q : Matrix (Fin n) (Fin n) ℂ} (hQ : IsUnit Q) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    Q * NormedSpace.exp (t • X) * Q⁻¹ = NormedSpace.exp (t • (Q * X * Q⁻¹)) := by
  rw [← Matrix.exp_conj Q _ hQ, Matrix.mul_smul, Matrix.smul_mul]

theorem model (h : GlobalTheory.Published.KFiniteVectorsUnitary) {lam : Fin n → ℝ} (hσ : IsDS ε lam σ)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hJ : Pᴴ * Jm ε * P = G) :
    (∃ p : kFinSub ε σ, p ≠ 0) ∧
    (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v : kFinSub ε σ, ∃ w : kFinSub ε σ,
      HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0) ∧
    ∀ B : Submodule ℂ (kFinSub ε σ), B ≠ ⊥ →
      (∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 → ∀ v w : kFinSub ε σ, v ∈ B →
        HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • X) * P⁻¹) (v : H)) (w : H) 0 → w ∈ B) → B = ⊤ := by
  haveI := hσ.1
  haveI := hσ.2.1
  obtain ⟨-, -, hd, hst, hirr⟩ := h.of_isDS hσ
  have hdet := (isUnit_iff_isUnit_det _).1 hP
  have h1 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ hdet
  have h2 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hG' : (P⁻¹)ᴴ * G * P⁻¹ = Jm ε := by
    rw [← hJ]
    calc _ = (P * P⁻¹)ᴴ * Jm ε * (P * P⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = _ := by rw [h2]; simp
  refine ⟨?_, fun X hX v => ?_, fun B hB hS => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨x, hx⟩ := exists_ne (0 : H)
    obtain ⟨y, hy, hy'⟩ := hd.exists_mem_open isOpen_compl_singleton ⟨x, hx⟩
    exact hy' (congrArg Subtype.val (hne ⟨y, hy⟩))
  · have hY : inG ε (P * X * P⁻¹) := conj_lie' h1 hG' hX
    refine ⟨⟨dRep σ (P * X * P⁻¹) v, hst _ hY _ v.2⟩, ?_⟩
    simp only [exp_smul_conj' hP]
    exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
  · have hle : B.map (kFinSub ε σ).subtype ≤ kFinSub ε σ := Submodule.map_subtype_le _ _
    have hs : IsLieStable ε σ (B.map (kFinSub ε σ).subtype) := by
      rintro Y hY _ ⟨v, hv, rfl⟩
      refine ⟨⟨dRep σ Y v, hst _ hY _ v.2⟩, hS (P⁻¹ * Y * P) (conj_lie' h2 hJ hY) v _ hv ?_, rfl⟩
      have e : P * (P⁻¹ * Y * P) * P⁻¹ = Y := by
        calc _ = (P * P⁻¹) * Y * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = Y := by rw [h2]; simp
      simp only [exp_smul_conj' hP, e]
      exact h.hasDerivAt hσ.2.2.1 hσ.2.2.2.1 v.2 hY
    rcases hirr _ hle hs with e | e
    · exact absurd ((Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_bot _).symm)) hB
    · exact (Submodule.map_injective_of_injective (kFinSub ε σ).injective_subtype)
        (e.trans (Submodule.map_subtype_top _).symm)

end Model

end GlobalTheory.KFinStruct
end

