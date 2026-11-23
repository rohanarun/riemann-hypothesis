module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0633
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2914
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmDivisionStepDecomposition
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogStep

variable {O E : Type} [CommRing O] [CommRing E] [Algebra O E] {d : ℕ}

theorem constantCoeff_up_eq_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (i : Fin d) : constantCoeff (up E μ i) = 0 := by
  rw [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hμ,
    map_zero]

theorem ql_add {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} {f g : MvPowerSeries (Fin d) E} (hf : QL μ N f) (hg : QL μ N g) :
    QL μ N (f + g) := by
  obtain ⟨f0, f1, f2⟩ := hf
  obtain ⟨g0, g1, g2⟩ := hg
  refine ⟨by rw [map_add (f := _), f0, g0, add_zero], fun i => ?_, fun α => ?_⟩
  · obtain ⟨a, ha, ha'⟩ := f1 i
    obtain ⟨b, hb, hb'⟩ := g1 i
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    simp only [lin, map_add (f := _)] at ha' hb' ⊢
    rw [ha', hb']
  · obtain ⟨a, ha, ha'⟩ := f2 α
    obtain ⟨b, hb, hb'⟩ := g2 α
    refine ⟨a + b, N.add_mem ha hb, ?_⟩
    rw [formalCoboundary_add (constantCoeff_up_eq_zero hμ), map_add (f := _), ha', hb', map_add (f := _)]

theorem ql_smul {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {N : Ideal O} (a : O) {f : MvPowerSeries (Fin d) E} (hf : QL μ N f) :
    QL μ N (algebraMap O E a • f) := by
  obtain ⟨f0, f1, f2⟩ := hf
  refine ⟨?_, fun i => ?_, fun α => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, f0,
      mul_zero]
  · obtain ⟨b, hb, hb'⟩ := f1 i
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    simp only [lin, coeff_smul] at hb' ⊢
    rw [hb', map_mul]
  · obtain ⟨b, hb, hb'⟩ := f2 α
    refine ⟨a * b, N.mul_mem_left a hb, ?_⟩
    rw [formalCoboundary_smul (constantCoeff_up_eq_zero hμ), coeff_smul, hb', map_mul]

theorem ql_zero {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    (N : Ideal O) : QL μ N (0 : MvPowerSeries (Fin d) E) := by
  refine ⟨map_zero _, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
  have := formalCoboundary_smul (constantCoeff_up_eq_zero (E := E) hμ) 0 0
  rw [zero_smul, zero_smul] at this
  rw [this, map_zero, map_zero]

theorem comb_add {ι : Type} [Fintype ι] (b b' : ι → O) (e : ι → MvPowerSeries (Fin d) E) :
    comb (b + b') e = comb b e + comb b' e := by
  simp only [comb, Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib]

theorem ql_comb {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O} (hμ : ∀ i, constantCoeff (μ i) = 0)
    {ι : Type} [Fintype ι] (b : ι → O) (e : ι → MvPowerSeries (Fin d) E)
    (he : ∀ i, QL μ ⊤ (e i)) : QL μ ⊤ (comb b e) := by
  unfold comb
  induction (Finset.univ : Finset ι) using Finset.cons_induction with
  | empty => rw [Finset.sum_empty]; exact ql_zero hμ _
  | cons i s hi ih => rw [Finset.sum_cons]; exact ql_add hμ (ql_smul hμ _ (he i)) ih

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E) (lb : Module.Basis (Fin k) O G.dual.Lie), (∀ i, QL c.μ ⊤ (e i)) → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → (∀ i, lin (e (Sum.inl i)) = Pi.single i 1) → (∀ j, c.IsLie (e (Sum.inr j)) (lb j)) → ∀ f, QL c.μ ⊤ f → ∃ (b : Fin d ⊕ Fin k → O) (s : MvPowerSeries (Fin d) O) (f₁ : MvPowerSeries (Fin d) E), QL c.μ ⊤ f₁ ∧ f = comb b e + map (algebraMap O E) s + (p : E) • f₁ := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c E _ _ hF k e lb hQe hcob hlin hLie f hf
  have hμ := c.isLaw.const
  have hinj : Function.Injective (algebraMap O E) := hF.inj
  have hc0 := constantCoeff_up_eq_zero (E := E) hμ

  let t : Fin d ⊕ Fin k → G.dual.Lie := Sum.elim (fun _ => 0) fun j => lb j
  have ht : ∀ i, c.IsLie (e i) (t i) := by
    rintro (i | j)
    · obtain ⟨l, hl, -⟩ := _root_.GlobalTheory.QLogTangent.main p C v O hv G d c E hF _ (hQe (Sum.inl i))
      have := ((_root_.GlobalTheory.LieLin.main p C v O hv G d c E hF _ _ l l 0 hl hl).2.2 (hcob i))
      subst this
      exact hl
    · exact hLie j

  have hcombS : ∀ (b : Fin d ⊕ Fin k → O) (S : Finset (Fin d ⊕ Fin k)),
      c.IsLie (∑ i ∈ S, algebraMap O E (b i) • e i) (∑ i ∈ S, b i • t i) ∧
        QL c.μ ⊤ (∑ i ∈ S, algebraMap O E (b i) • e i) := by
    intro b S
    induction S using Finset.cons_induction with
    | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact ⟨c.isLie_zero hinj, ql_zero hμ _⟩
    | cons i s hi ih =>
      rw [Finset.sum_cons, Finset.sum_cons, add_comm, add_comm (b i • t i)]
      exact ⟨(_root_.GlobalTheory.LieLin.main p C v O hv G d c E hF _ _ _ _ (b i) ih.1 (ht i)).1 ih.2 (hQe i),
        ql_add hμ ih.2 (ql_smul hμ _ (hQe i))⟩
  have hcombLie : ∀ b : Fin d ⊕ Fin k → O, c.IsLie (comb b e) (∑ i, b i • t i) :=
    fun b => (hcombS b Finset.univ).1

  obtain ⟨l, hl, -⟩ := _root_.GlobalTheory.QLogTangent.main p C v O hv G d c E hF f hf
  let b0 : Fin d ⊕ Fin k → O := Sum.elim (0 : Fin d → O) fun j => lb.repr l j
  have hb0 : ∑ i, b0 i • t i = l := by
    rw [Fintype.sum_sum_type]
    simp only [b0, t, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zero_smul, Finset.sum_const_zero,
      zero_add]
    exact lb.sum_repr l
  set f' := f + algebraMap O E (-1) • comb b0 e with hf'
  have hQf' : QL c.μ ⊤ f' := ql_add hμ hf (ql_smul hμ _ (ql_comb hμ b0 e hQe))
  have hLf' : c.IsLie f' ((p : O) • 0) := by
    have := (_root_.GlobalTheory.LieLin.main p C v O hv G d c E hF f (comb b0 e) l _ (-1) hl (hcombLie b0)).1 hf
      (ql_comb hμ b0 e hQe)
    rwa [hb0, neg_one_smul, add_neg_cancel, ← smul_zero (p : O)] at this
  obtain ⟨s, g, hg, hh⟩ := _root_.GlobalTheory.QLogInj.main p C v O hv G d c E hF f' 0 hQf' hLf'
  set h := f' - map (algebraMap O E) s - g with hhdef

  have hw : ∀ i, ∃ w : O, lin g i = algebraMap O E w := by
    intro i
    obtain ⟨b1, -, hb1⟩ := hQf'.2.1 i
    obtain ⟨b3, -, hb3⟩ := hh.2.1 i
    refine ⟨b1 - coeff (Finsupp.single i 1) s - b3, ?_⟩
    have : g = f' - map (algebraMap O E) s - h := by rw [hhdef]; ring
    simp only [lin] at hb1 hb3 ⊢
    rw [this, map_sub, map_sub, hb1, hb3, coeff_map, map_sub, map_sub]
  choose w hw using hw
  let bw : Fin d ⊕ Fin k → O := Sum.elim w 0
  have hcw : comb bw e = ∑ i, algebraMap O E (w i) • e (Sum.inl i) := by
    simp [comb, bw, Fintype.sum_sum_type]

  have hgw : g = comb bw e := by
    have key := _root_.GlobalTheory.LogUniq.eq_zero_of_linear_zero_coboundary_zero_fractions p O E hF d c.μ c.isLaw (g - comb bw e) ?_ ?_
    · exact sub_eq_zero.1 key
    · funext i
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lin, hcw, map_sub, map_sum, coeff_smul, Pi.zero_apply] at hw ⊢
      have hl' : ∀ j, coeff (Finsupp.single i 1) (e (Sum.inl j)) =
          (Pi.single j (1 : E) : Fin d → E) i := fun j => congrFun (hlin j) i
      simp only [hl', hw]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, Ne.symm hj]) (by simp)]
      simp
    · let L : MvPowerSeries (Fin d) E →+ MvPowerSeries (Fin d ⊕ Fin d) E :=
        AddMonoidHom.mk' (cob1 (up E c.μ)) (formalCoboundary_add hc0)
      have hL : ∀ x, L x = cob1 (up E c.μ) x := fun _ => rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hL, map_sub, hcw, map_sum]
      simp only [hL, formalCoboundary_smul hc0, hcob, smul_zero, Finset.sum_const_zero, sub_zero]
      exact hg

  obtain ⟨u, hu⟩ := hF.unit_p
  refine ⟨bw + b0, s, (↑u⁻¹ : E) • h, ?_, ?_⟩
  · obtain ⟨h0, h1, h2⟩ := hh
    refine ⟨?_, fun i => ?_, fun α => ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0,
        mul_zero]
    · obtain ⟨b, hb, hb'⟩ := h1 i
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      simp only [lin, coeff_smul] at hb' ⊢
      rw [hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul, one_mul]
    · obtain ⟨b, hb, hb'⟩ := h2 α
      obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton.1 hb
      refine ⟨b', trivial, ?_⟩
      rw [formalCoboundary_smul hc0, coeff_smul, hb', map_mul, map_natCast, ← hu, ← mul_assoc, Units.inv_mul,
        one_mul]
  · rw [smul_smul, ← hu, Units.mul_inv, one_smul, comb_add, ← hgw]
    rw [map_neg, map_one, neg_one_smul] at hf'
    rw [hhdef, hf']
    ring

end GlobalTheory.QLogStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudCechRelationDlogDescendsToAbelianPart
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Heat.AbDescent

theorem pbT_id {X : Scheme.{0}} {U V : X.Opens} (hV : V ≤ U) (s : Γ(X, U)) : pbT (𝟙 X) s V = rsT s V := by
  rw [GlobalTheory.KS.pbT_of_le (𝟙 X) hV, GlobalTheory.KS.rsT_of_le hV]
  simp [Scheme.Hom.appLE, resG]
  rfl

theorem pbT_pbT_id {Z X : Scheme.{0}} (q : Z ⟶ X) {U V : X.Opens} (hV : V ≤ U) {W : Z.Opens} (hW : W ≤ q ⁻¹ᵁ V)
    (s : Γ(X, U)) : pbT q (pbT (𝟙 X) s V) W = pbT q s W := by
  rw [pbT_id hV, GlobalTheory.KS.pbT_rsT q hV hW]

theorem descent : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  intro R _ _ Q O _ _ _ oa Y δH δ hpb K Wk jk hV hcov hle P hP hrel
  have := Y.smooth_q
  have := (AbConst.surjective_q Y).1
  choose V hV using hV
  have hb : ∀ k, ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b (Wk k) = P k := by
    intro k
    have key : ∀ (W : Y.H.left.Opens) (hW : W = Y.q.left ⁻¹ᵁ V k) (p : Γ(Y.H.left, W)), IsWt Y 0 W p →
        ∃ b : Γ(Q.P.A.left, V k), pbT Y.q.left b W = p := by
      intro W hW p hp
      subst hW
      obtain ⟨a, ha⟩ := AbConst.exists_app_eq Y hp
      exact ⟨a, by rw [GlobalTheory.KS.pbT_of_le _ le_rfl, ← ha, Scheme.Hom.app_eq_appLE]⟩
    exact key _ (hV k) _ (hP k)
  choose b hb using hb
  have hVle : ∀ k, V k ≤ Q.P.L.U (jk k) := by
    intro k y hy
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ Wk k := by rw [hV k]; exact hy
    exact hle k hx
  refine ⟨V, b, ?_, hVle, ?_⟩
  · rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Wk k := by rw [hcov]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at hx ⊢
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [hV k] at hk; exact hk⟩
  · intro k k'
    have hWo : Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk k ⊓ Wk k' := by
      rw [hV k, hV k']
      exact fun x hx => ⟨hx.1, hx.2⟩
    have h := hrel k k' _ hWo
    apply FunDescent.app_injective Y.q.left (V k ⊓ V k')
    have e : ∀ s : Γ(Q.P.A.left, V k ⊓ V k'),
        (Y.q.left.app (V k ⊓ V k')).hom s = pbT Y.q.left s (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := fun s => by
      rw [GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
    rw [e, e, GlobalTheory.KS.pbT_sub, GlobalTheory.KS.pbT_rsT _ inf_le_right le_rfl, GlobalTheory.KS.pbT_rsT _ inf_le_left le_rfl]
    have hbk : ∀ j, Y.q.left ⁻¹ᵁ (V k ⊓ V k') ≤ Wk j →
        pbT Y.q.left (b j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) = rsT (P j) (Y.q.left ⁻¹ᵁ (V k ⊓ V k')) := by
      intro j hj
      rw [← hb j, GlobalTheory.KS.rsT_pbT _ (hV j).le hj]
    rw [hbk k' (hWo.trans inf_le_right), hbk k (hWo.trans inf_le_left), h]
    have hUo : V k ⊓ V k' ≤ Q.P.L.U (jk k) ⊓ Q.P.L.U (jk k') := inf_le_inf (hVle k) (hVle k')
    unfold dlg
    rw [GlobalTheory.KS.pbT_mul, ← hpb (V k ⊓ V k') (pbT (𝟙 _) (Q.P.L.g (jk k) (jk k')).val (V k ⊓ V k')) _ le_rfl,
      pbT_pbT_id _ hUo le_rfl, pbT_pbT_id _ hUo le_rfl]

end GlobalTheory.Heat.AbDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudSectionIdentityOfGenericFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.RayFlatDesc

theorem gs_sub_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by
  simp only [gs, dif_pos h, map_sub]

theorem gs_zero_of {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (ρ τ : SecM Y.q.left Q.P.L k) (a b : R), (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (r : Z ⟶ Y.H.left), r ≫ Y.H.hom = g ≫ jK R → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J) → ∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → gs r z ⊤ (scal Y.H.hom a) * sval ρ r z J = gs r z ⊤ (scal Y.H.hom b) * sval τ r z J := by
  intro R _ _ Q O _ _ _ oa Y k ρ τ a b H Z r z J hJ
  have := GlobalTheory.RayTan.smooth_H R Q O oa Y
  have hL : Q.P.L.IsLB := Q.P.isLB
  have key : ∀ j : Fin 1 → Q.P.L.ι,
      (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom a) * ρ.f j -
        (Y.H.left.presheaf.map (homOfLE le_top).op).hom (scal Y.H.hom b) * τ.f j = 0 := by
    intro j
    apply GlobalTheory.Mum.fst_generic_app_injective Y.H.hom _
    rw [map_zero]
    apply fn_ext
    intro y hy
    have hy' : pullback.fst Y.H.hom (jK R) y ∈
        (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U j := hy
    have hw : pullback.fst Y.H.hom (jK R) y ∈ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) j := hy
    obtain ⟨J', hJ', e⟩ := exists_good Q.P.L hL y (fun _ : Unit => pullback.fst Y.H.hom (jK R) ≫ Y.q.left)
      (fun _ => j 0) (fun _ _ _ => rfl) (fun _ => Set.mem_iInter.1 hw 0)
    have ej : ∀ i : Fin 1, J' (pullback.fst Y.H.hom (jK R) ≫ Y.q.left) = j i := fun i => by
      rw [Subsingleton.elim i 0]; exact e ()
    have h1 := H _ (pullback.snd _ _) (pullback.fst _ _) pullback.condition y J' hJ'
    rw [sval_of ρ _ y J' j ej, sval_of τ _ y J' j ej] at h1
    rw [gs_pull (𝟙 _) (pullback.fst Y.H.hom (jK R)) y _ hy', Category.id_comp, gs_zero_of _ _ _,
      gs_sub_of _ _ _ hy', gs_mul _ _ _ hy', gs_mul _ _ _ hy', gs_res _ _ _ hy', gs_res _ _ _ hy']
    exact sub_eq_zero.2 h1
  have hm : r z ∈ (LB.LinComb Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => (k : ℤ))).U
      (fun _ => J (r ≫ Y.q.left)) :=
    Set.mem_iInter.2 fun _ => hJ (r ≫ Y.q.left)
  have e := congrArg (gs r z _) (key fun _ => J (r ≫ Y.q.left))
  rw [gs_sub_of _ _ _ hm, gs_mul _ _ _ hm, gs_mul _ _ _ hm, gs_res _ _ _ hm, gs_res _ _ _ hm, gs_zero_of _ _ _,
    sub_eq_zero] at e
  rw [sval_of ρ r z J _ (fun _ => rfl), sval_of τ r z J _ (fun _ => rfl)]
  exact e

end GlobalTheory.RayFlatDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudWeightZeroCompatibleFunctionsEqBaseConsta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConstGlob

open GlobalTheory.KS.GlueDer

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa)

theorem app_rsT {U V : Q.P.A.left.Opens} (h : V ≤ U) (a : Γ(Q.P.A.left, U)) :
    (Y.q.left.app V).hom (rsT a V) = rsT ((Y.q.left.app U).hom a) (Y.q.left ⁻¹ᵁ V) := by
  rw [rsT_eq h, rsT_eq (pre_mono _ h), res_app]

theorem app_constFn (V : Q.P.A.left.Opens) (r : R) :
    (Y.q.left.app V).hom (constFn Q.P.A.hom V r) = constFn Y.H.hom _ r :=
  app_const (RingHom.id R) Q.P.A.hom Y.H.hom Y.q.left
    ((Over.w Y.q).trans ((Category.comp_id _).symm.trans (congrArg (Y.H.hom ≫ ·) (Spec.map_id _).symm))) V r

theorem exists_constFn_top (t : Γ(Q.P.A.left, ⊤)) : ∃ r : R, t = constFn Q.P.A.hom ⊤ r := by
  obtain ⟨s, rfl⟩ := (GlobalTheory.allSixLaws.1.globalFns (Sp R) Q.P.A Q.P.isAb).2 t
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom s, ?_⟩
  simp only [constFn]
  rw [Iso.hom_inv_id_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  rfl

theorem exists_const_of_preimage [IsLocalRing R] [IsNoetherianRing R] {K : Type} (V : K → Q.P.A.left.Opens)
    (hc : ⨆ k, Y.q.left ⁻¹ᵁ V k = ⊤) (F : ∀ k, Γ(Y.H.left, Y.q.left ⁻¹ᵁ V k)) (hF : ∀ k, IsWt Y 0 _ (F k))
    (hag : ∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Y.q.left ⁻¹ᵁ V k ⊓ Y.q.left ⁻¹ᵁ V k' →
      rsT (F k) Wo = rsT (F k') Wo) :
    ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  have := Y.smooth_q
  have := (GlobalTheory.Heat.AbConst.surjective_q Y).1
  have inj := FunDescent.app_injective Y.q.left
  choose a ha using fun k => GlobalTheory.Heat.AbConst.exists_app_eq Y (hF k)
  have cov : (⊤ : Q.P.A.left.Opens) ≤ ⨆ k, V k := by
    intro y _
    obtain ⟨x, rfl⟩ := Y.q.left.surjective y
    have hx : x ∈ ⨆ k, Y.q.left ⁻¹ᵁ V k := by rw [hc]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩
  obtain ⟨t, ht⟩ := GlobalTheory.KS.exists_rsT_eq V (O := ⊤) (fun _ => le_top) cov a fun k l => by
    apply inj
    rw [app_rsT Y inf_le_left, app_rsT Y inf_le_right, ha, ha]
    exact hag k l _ (le_inf (pre_mono _ inf_le_left) (pre_mono _ inf_le_right))
  obtain ⟨r, rfl⟩ := exists_constFn_top t
  refine ⟨r, fun k => ?_⟩
  rw [← ha, ← ht k, GlobalTheory.KS.rsT_constFn _ le_top, app_constFn]

end GlobalTheory.Heat.AbConstGlob

open GlobalTheory.Heat.AbConstGlob in
theorem GlobalTheory.Heat.AbConstGlob.main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  intro R _ _ _ _ Q O _ _ _ oa Y K Wk hW hc F hF hag
  choose V hV using hW
  obtain rfl : Wk = fun k => Y.q.left ⁻¹ᵁ V k := funext hV
  exact exists_const_of_preimage Y V hc F hF hag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellation
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem actPB_cancel : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S)
    (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂)
    (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  intro h M B _ ζ O _ S S₁ S₂ s s₁ s₂ z act g₁ y w₁ act₁ w₂ act₂ m₁ m₂
  obtain ⟨φ₁, φ₁₂, h1, s1, p1, l1, a1⟩ := m₁
  obtain ⟨φ₂, φ₂₂, h2, s2, p2, l2, a2⟩ := m₂
  have hw : φ₂ ≫ z.A.hom = (w₂.A.hom ≫ y) ≫ g₁ := by rw [h2.1.w, Category.assoc]
  let ψ : w₂.A.left ⟶ w₁.A.left := h1.1.lift φ₂ (w₂.A.hom ≫ y) hw
  have hψ₁ : ψ ≫ φ₁ = φ₂ := h1.1.lift_fst _ _ _
  have hψ : ψ ≫ w₁.A.hom = w₂.A.hom ≫ y := h1.1.lift_snd _ _ _
  let ψ₂ : (G2 w₂.A).left ⟶ (G2 w₁.A).left := ActUnr.sqMap hψ
  have sψ : IsSquare ψ ψ₂ := ⟨ActUnr.sqMap_fst hψ, ActUnr.sqMap_snd hψ⟩
  have e₂ : φ₂₂ = ψ₂ ≫ φ₁₂ := by
    apply ActUnr.left_hom_ext
    · rw [s2.1, Category.assoc, s1.1, ← Category.assoc, sψ.1, Category.assoc, hψ₁]
    · rw [s2.2, Category.assoc, s1.2, ← Category.assoc, sψ.2, Category.assoc, hψ₁]
  have n : IsGrpPullback w₂.A z.A (y ≫ g₁) (ψ ≫ φ₁) := by rw [hψ₁]; exact h2
  refine ⟨ψ, ψ₂, IsGrpPullback.cancel h1 n hψ, sψ, ?_, fun a => ?_, fun o => ?_⟩
  · refine LBIso.trans w₂.isLB (pull_isLB z.isLB _) (pull_isLB w₁.isLB _) p2 ?_
    refine LBIso.trans (pull_isLB z.isLB _) (pull_isLB (pull_isLB z.isLB _) _) (pull_isLB w₁.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull z.isLB ψ₂ e₂) ?_
    exact GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm p1) ψ₂
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, l2 a, Category.assoc, Category.assoc, l1 a]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (w₂.lev a), Category.assoc, Over.w (w₁.lev a)]
      simp
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, a2 o, Category.assoc, a1 o, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (act₂ o), Category.assoc, Over.w (act₁ o), hψ]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecHomExtOfLocalizationAtPrimes
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpecLocalExt

theorem hom_ext_of_localizationAtPrime : ∀ (A : Type) [CommRing A] (X : Scheme.{0}) (a b : Sp A ⟶ X), (∀ (P : Ideal A) [P.IsPrime], spMap (algebraMap A (Localization.AtPrime P)) ≫ a = spMap (algebraMap A (Localization.AtPrime P)) ≫ b) → a = b := by
  intro A _ X a b h
  refine GlobalTheory.hom_ext_of_isLocalRing fun B _ _ φ => ?_
  let P : Ideal A := (IsLocalRing.maximalIdeal B).comap φ
  haveI : P.IsPrime := Ideal.comap_isPrime φ (IsLocalRing.maximalIdeal B)
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y => by
    by_contra hy
    exact y.2 ((IsLocalRing.mem_maximalIdeal _).2 hy)
  let ψ : Localization.AtPrime P →+* B := IsLocalization.lift hu
  have e : φ = ψ.comp (algebraMap A (Localization.AtPrime P)) := (IsLocalization.lift_comp hu).symm
  have h' := h P
  simp only [spMap] at h'
  rw [e, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc, h']

end GlobalTheory.SpecLocalExt
end
end

