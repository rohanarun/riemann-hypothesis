module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCechNerveBaseChangeIsPullback
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct
open GlobalTheory.EtC hiding cechAug

namespace GlobalTheory.CechBC

universe v u

theorem widePullback_isPullback {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (hP : IsPullback a f' f b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] :
    IsPullback
      (WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, hP.w, ← Category.assoc, WidePullback.π_arrow]))
      (WidePullback.base (fun _ : Fin (n + 1) => f')) (WidePullback.base (fun _ : Fin (n + 1) => f)) b := by
  refine IsPullback.of_isLimit' ⟨WidePullback.lift_base _ _ _ _⟩ (PullbackCone.IsLimit.mk _
    (fun s => WidePullback.lift s.snd
      (fun i => hP.lift (s.fst ≫ WidePullback.π _ i) s.snd
        (by rw [Category.assoc, WidePullback.π_arrow, s.condition]))
      (fun i => hP.lift_snd _ _ _)) ?_ ?_ ?_)
  · intro s
    apply WidePullback.hom_ext
    · intro j
      rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, IsPullback.lift_fst]
    · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, s.condition]
  · intro s
    exact WidePullback.lift_base _ _ _ _
  · intro s m h1 h2
    apply WidePullback.hom_ext
    · intro j
      apply hP.hom_ext
      · rw [WidePullback.lift_π, IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, WidePullback.lift_π]
      · rw [WidePullback.lift_π, IsPullback.lift_snd, Category.assoc, WidePullback.π_arrow, h2]
    · rw [WidePullback.lift_base, h2]

theorem lift_comp_lift {C : Type u} [Category.{v} C] {Y X Y' X' : C}
    {a : Y' ⟶ Y} {f' : Y' ⟶ X'} {f : Y ⟶ X} {b : X' ⟶ X} (w : a ≫ f = f' ≫ b) (n : ℕ)
    [HasWidePullback X' (fun _ : Fin (n + 1) => Y') (fun _ => f')]
    [HasWidePullback X (fun _ : Fin (n + 1) => Y) (fun _ => f)] {T : C}
    (g : T ⟶ X') (e : Fin (n + 1) → (T ⟶ Y')) (he : ∀ i, e i ≫ f' = g)
    (g₂ : T ⟶ X) (e₂ : Fin (n + 1) → (T ⟶ Y)) (he₂ : ∀ i, e₂ i ≫ f = g₂)
    (hg : g ≫ b = g₂) (hh : ∀ i, e i ≫ a = e₂ i) :
    WidePullback.lift g e he ≫
      WidePullback.lift (WidePullback.base (fun _ : Fin (n + 1) => f') ≫ b)
        (fun i => WidePullback.π (fun _ : Fin (n + 1) => f') i ≫ a)
        (fun i => by rw [Category.assoc, w, ← Category.assoc, WidePullback.π_arrow]) =
      WidePullback.lift g₂ e₂ he₂ := by
  apply WidePullback.hom_ext
  · intro j
    rw [Category.assoc, WidePullback.lift_π, ← Category.assoc, WidePullback.lift_π, WidePullback.lift_π, hh]
  · rw [Category.assoc, WidePullback.lift_base, ← Category.assoc, WidePullback.lift_base, WidePullback.lift_base, hg]

end GlobalTheory.CechBC


open GlobalTheory.CechBC in
theorem GlobalTheory.cech_baseChange : ∀ (Y X Y' X' : Scheme.{0}) (a : Y' ⟶ Y) (f' : Y' ⟶ X') (f : Y ⟶ X) (b : X' ⟶ X), IsPullback a f' f b → ∃ m : cech f' ⟶ cech f, IsPullback m (_root_.GlobalTheory.EtC.cechAug f') (_root_.GlobalTheory.EtC.cechAug f) (sch.map b) ∧ ∀ (k : ℕ) (U : Scheme.{0}) (x : U ⟶ X') (y : Fin (k + 1) → (U ⟶ Y')) (h : ∀ i, y i ≫ f' = x), ∃ h', (m.app (op (SimplexCategory.mk (k)))).app (op U) (cechPt f' k x y h) = cechPt f k (x ≫ b) (fun i => y i ≫ a) h' := by
  intro Y X Y' X' a f' f b hP
  have hw : yoneda.map a ≫ yoneda.map f = yoneda.map f' ≫ yoneda.map b := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, hP.w]
  have hY : IsPullback (yoneda.map a) (yoneda.map f') (yoneda.map f) (yoneda.map b) := hP.map yoneda
  refine ⟨Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw), ?_, ?_⟩
  · refine IsPullback.of_forall_isPullback_app (fun n => ?_)
    exact widePullback_isPullback hY n.unop.len
  · intro k U x y h
    have h' : ∀ i, (y i ≫ a) ≫ f = x ≫ b := fun i => by rw [Category.assoc, hP.w, ← Category.assoc, h i]
    refine ⟨h', ?_⟩
    have key : WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f') (yoneda.map x) (fun i => yoneda.map (y i))
        (fun i => by rw [← yoneda.map_comp, h i]) ≫
        (Arrow.mapCechNerve (Arrow.homMk' (f := yoneda.map f') (g := yoneda.map f) (yoneda.map a) (yoneda.map b) hw)).app (op (SimplexCategory.mk k)) =
        WidePullback.lift (arrows := fun _ : Fin (k + 1) => yoneda.map f) (yoneda.map (x ≫ b)) (fun i => yoneda.map (y i ≫ a))
        (fun i => by rw [← yoneda.map_comp, h' i]) := by
      exact lift_comp_lift hw k _ _ _ _ _ _ (yoneda.map_comp x b).symm (fun i => (yoneda.map_comp (y i) a).symm)
    unfold cechPt
    erw [← NatTrans.comp_app_apply]
    exact congrArg (fun φ : yoneda.obj U ⟶ (cech f).obj (op (SimplexCategory.mk k)) => φ.app (op U) (𝟙 U)) key
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicProperties
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem ev_basic : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ},
    (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧
      ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧
      ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧
      ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
      Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧
    (∀ α β : Cochain ((chains R).obj E) I n,
      (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧
    (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U),
      ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧
    ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x,
      ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x) := by
  intro R _ E I n
  refine ⟨fun α β p s h U x => ⟨CupSpec.ev_add α β p s h U x,
      map_sub (CupSpec.evHom I n p s h U x) α β, CupSpec.ev_zero p s h U x,
      fun c => CupSpec.ev_zsmul c α p s h U x⟩,
    fun α p s h V U g x => CupSpec.ev_res α p s h g x,
    fun α β H => CupSpec.ev_ext α β H,
    fun f α p s h U x => CupSpec.ev_pull f α p s h U x, ?_⟩
  intro J m α p s h U x
  rw [CupSpec.ev_def, CupSpec.ev_def, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, ← Category.assoc]
  rfl

end GlobalTheory.EtC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValues
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory

theorem ev_delta_values : ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
    (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
    (∀ (x : Sx E 0 U), EtC.ev (δ n m α) 0 m (by simp) U x =
      Sec.map (I.d n m) (EtC.ev α 0 n (by simp) U x)) ∧
    ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
      EtC.ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (EtC.ev α (p + 1) s hs U x) +
        m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • EtC.ev α p t (by omega) U (x.face i) := by
  intro R _ E I n m hm α U
  exact ⟨fun x => CupSpec.ev_δ_zero hm α U n m (by simp) (by simp) x,
    fun p s t hs ht x => CupSpec.ev_δ_succ hm α U p s t hs ht x⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainShortExactOfInjectiveTerms
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.cochain_shortExact_of_injective :
    ∀ (R : Type) [CommRing R] (I : _root_.GlobalTheory.EtC.Cx R), (∀ n, Injective (I.X n)) → ∀ (S : ShortComplex (_root_.GlobalTheory.EtC.Cx R)), S.ShortExact → ∀ n : ℤ, (∀ a : Cochain S.X₁ I n, ∃ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = a) ∧ (∀ b : Cochain S.X₂ I n, (Cochain.ofHom S.f).comp b (zero_add n) = 0 → ∃ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = b) ∧ ∀ c : Cochain S.X₃ I n, (Cochain.ofHom S.g).comp c (zero_add n) = 0 → c = 0 := by
  intro R _ I hI S hS n
  have hp : ∀ p : ℤ, (S.map (HomologicalComplex.eval _ _ p)).ShortExact :=
    fun p => hS.map_of_exact _
  have hmono : ∀ p : ℤ, Mono (S.f.f p) := fun p => (hp p).mono_f
  have hepi : ∀ p : ℤ, Epi (S.g.f p) := fun p => (hp p).epi_g
  refine ⟨fun a => ?_, fun b hb => ?_, fun c hc => ?_⟩
  · refine ⟨Cochain.mk (fun p q h => Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    ext p q h
    simp
  · have hb' : ∀ p q (h : p + n = q), S.f.f p ≫ b.v p q h = 0 := by
      intro p q h
      have := Cochain.congr_v hb p q h
      simpa using this
    refine ⟨Cochain.mk (fun p q h =>
      (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).1), ?_⟩
    refine Cochain.ext _ _ (fun p q h => ?_)
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.mk_v]
    exact (CokernelCofork.IsColimit.desc' (hp p).gIsCokernel (b.v p q h) (hb' p q h)).2
  · refine Cochain.ext _ _ (fun p q h => ?_)
    have := Cochain.congr_v hc p q h
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.zero_v] at this
    simpa using (cancel_epi (S.g.f p)).mp (this.trans (comp_zero).symm)

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.InjResCmp

variable {R : Type} [CommRing R]

theorem cpush_id (K I : Cx R) (n : ℤ) (x : CohomologyClass K I n) : cpush K (𝟙 I) n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp]

theorem cpush_comp (K : Cx R) {I J L : Cx R} (f : I ⟶ J) (g : J ⟶ L) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K (f ≫ g) n x = cpush K g n (cpush K f n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [zcomp, Cochain.ofHom_comp]

theorem cpush_homotopy (K : Cx R) {I J : Cx R} {f g : I ⟶ J} (h : Homotopy f g) (n : ℤ) (x : CohomologyClass K I n) :
    cpush K f n x = cpush K g n x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
  change CohomologyClass.mk _ = CohomologyClass.mk _
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff,
    mem_coboundaries_iff _ (n - 1) (by omega)]
  refine ⟨x.1.comp z (by omega), ?_⟩
  rw [δ_comp x.1 z (by omega) (n + 1) 0 n (by omega) (by omega) (by omega)]
  simp [zcomp, hz, Cochain.comp_add]

open DerivedCategory in
theorem exists_quasiIso (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C) [QuasiIso ε] [(res R M).IsKInjective] :
    ∃ u : C ⟶ res R M, QuasiIso u := by
  letI := HasDerivedCategory.standard (Shv R)
  have : QuasiIso (resAug M) := (inferInstance : QuasiIso (injectiveResolution M).ι')
  let e : Q.obj C ≅ Q.obj (res R M) := (asIso (Q.map ε)).symm ≪≫ asIso (Q.map (resAug M))
  obtain ⟨g, hg⟩ := (CochainComplex.IsKInjective.Qh_map_bijective ((HomotopyCategory.quotient _ _).obj C)
    (res R M)).surjective
    ((quotientCompQhIso (Shv R)).hom.app C ≫ e.hom ≫ (quotientCompQhIso (Shv R)).inv.app (res R M))
  obtain ⟨u, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨u, ?_⟩
  rw [← isIso_Q_map_iff_quasiIso]
  have h1 := quotientCompQhIso_hom_naturality u
  have h2 : Q.map u = (quotientCompQhIso (Shv R)).inv.app C ≫ Qh.map ((HomotopyCategory.quotient _ _).map u) ≫
      (quotientCompQhIso (Shv R)).hom.app (res R M) := by
    rw [h1]; simp
  rw [h2, hg]
  infer_instance

theorem hyper_iso_of_injective_resolution : ∀ (R : Type) [CommRing R] (M : Shv R) (C : Cx R) (ε : sgl M ⟶ C),
    C.IsStrictlyGE 0 → (∀ t, Injective (C.X t)) → QuasiIso ε → ∀ (K : Cx R) (n : ℤ),
    Nonempty (HK R K M n ≃+ CohomologyClass K C n) := by
  intro R _ M C ε hC hI hε K n
  haveI := hC
  haveI : ∀ t, Injective (C.X t) := hI
  haveI := hε
  haveI : C.IsKInjective := isKInjective_of_injective C 0
  haveI : (res R M).IsKInjective := (inferInstance : (injectiveResolution M).cochainComplex.IsKInjective)
  obtain ⟨u, hu⟩ := exists_quasiIso M C ε
  obtain ⟨e, -⟩ := (CochainComplex.IsKInjective.quasiIso_iff u).1 hu
  exact ⟨{ toFun := cpush K e.inv n
           invFun := cpush K e.hom n
           left_inv := fun x => by
             change cpush K e.hom n (cpush K e.inv n x) = x
             rw [← cpush_comp, cpush_homotopy K e.homotopyInvHomId, cpush_id]
           right_inv := fun y => by
             change cpush K e.inv n (cpush K e.hom n y) = y
             rw [← cpush_comp, cpush_homotopy K e.homotopyHomInvId, cpush_id]
           map_add' := map_add _ }⟩

end GlobalTheory.EtC.InjResCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPropertyCalculusRules
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem loc_of_forall (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ V g, P V g) : Loc U P :=
  ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => h V g⟩

theorem loc_mono (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

theorem loc_and (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (hP : Loc U P) (hQ : Loc U Q) : Loc U fun V g => P V g ∧ Q V g := by
  obtain ⟨S, hS, hP⟩ := hP
  obtain ⟨T, hT, hQ⟩ := hQ
  exact ⟨S ⊓ T, Scheme.etaleTopology.intersection_covering hS hT,
    fun V g hg => ⟨hP V g hg.1, hQ V g hg.2⟩⟩

theorem loc_pullback (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U P) : Loc W fun V g => P V (g ≫ k) := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S.pullback k, Scheme.etaleTopology.pullback_stable k hS, fun V g hg => hP V (g ≫ k) hg⟩

theorem loc_trans (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : Loc U (fun V g => Loc V fun W k => P W (k ≫ g))) : Loc U P := by
  obtain ⟨S, hS, hloc⟩ := h
  let R : Sieve U :=
    { arrows := fun W h => ∀ (W' : Scheme.{0}) (k : W' ⟶ W), P W' (k ≫ h)
      downward_closed := fun {W W'} h hh k W'' k' => by
        simpa [Category.assoc] using hh W'' (k' ≫ k) }
  refine ⟨R, Scheme.etaleTopology.transitive hS R ?_, fun V g hg => by simpa using hg V (𝟙 V)⟩
  intro V g hg
  obtain ⟨T, hT, hP⟩ := hloc V g hg
  refine Scheme.etaleTopology.superset_covering ?_ hT
  intro W k hk W' k'
  have := hP W' (k' ≫ k) (T.downward_closed hk k')
  simpa [Category.assoc] using this

theorem loc_top (U : Scheme.{0}) : Loc U fun _ _ => True :=
  loc_of_forall U _ fun _ _ => trivial

theorem loc_finset (U : Scheme.{0}) {ι : Type} (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) (s : Finset ι) : Loc U fun V g => ∀ i ∈ s, P i V g := by
  classical
  induction s using Finset.induction_on with
  | empty => exact loc_of_forall U _ fun V g i hi => absurd hi (Finset.notMem_empty i)
  | insert a s ha ih =>
    refine loc_mono U _ _ (loc_and U _ _ (h a) ih) ?_
    intro V g hg i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hg.1
    · exact hg.2 i hi

theorem loc_finite (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop)
    (h : ∀ i, Loc U (P i)) : Loc U fun V g => ∀ i, P i V g := by
  have := Fintype.ofFinite ι
  exact loc_mono U _ _ (loc_finset U P h Finset.univ) fun V g hg i => hg i (Finset.mem_univ i)

theorem loc_of_isEmpty (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop) :
    Loc U P :=
  ⟨⊥, Scheme.bot_mem_grothendieckTopology U, fun V g hg => hg.elim⟩

theorem loc_calculus :
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ V g, P V g) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → (∀ V g, P V g → Q V g) → Loc U Q) ∧
    (∀ (U : Scheme.{0}) (P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc U Q → Loc U fun V g => P V g ∧ Q V g) ∧
    (∀ (U W : Scheme.{0}) (k : W ⟶ U) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P → Loc W fun V g => P V (g ≫ k)) ∧
    (∀ (U : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U (fun V g => Loc V fun W k => P W (k ≫ g)) → Loc U P) ∧
    (∀ (U : Scheme.{0}) (ι : Type) [Finite ι] (P : ι → ∀ V : Scheme.{0}, (V ⟶ U) → Prop), (∀ i, Loc U (P i)) → Loc U fun V g => ∀ i, P i V g) ∧
    (∀ (U : Scheme.{0}) [IsEmpty U] (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop), Loc U P) :=
  ⟨loc_of_forall, loc_mono, loc_and, loc_pullback, loc_trans, loc_finite, loc_of_isEmpty⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeTensorOfEtaleAway
section
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem etale_localization_atPrime_tensor_of_etale_away : ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] (b : R),
    Algebra.Etale R (Localization.Away (algebraMap R C b)) →
    ∀ (P : Ideal R) [P.IsPrime], b ∉ P →
      Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ b hE P _ hb
  let Rp := Localization.AtPrime P
  let Cb := Localization.Away (algebraMap R C b)
  haveI : Algebra.Etale Rp (Rp ⊗[R] Cb) := Algebra.Etale.baseChange R Cb Rp
  have hu : IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).toRingHom
      (algebraMap R C b)) := by
    change IsUnit ((Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C) (algebraMap R C b))
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R Rp (Rp ⊗[R] C)]
    exact (IsLocalization.map_units Rp (⟨b, hb⟩ : P.primeCompl)).map _
  let g0 : Cb →+* Rp ⊗[R] C := IsLocalization.Away.lift (algebraMap R C b) hu
  have hg0 : ∀ c : C, g0 (algebraMap C Cb c) = (1 : Rp) ⊗ₜ[R] c := fun c =>
    IsLocalization.Away.lift_eq (algebraMap R C b) hu c
  let g : Cb →ₐ[R] Rp ⊗[R] C :=
    { g0 with
      commutes' := fun r => by
        change g0 (algebraMap R Cb r) = _
        rw [IsScalarTower.algebraMap_apply R C Cb, hg0]
        exact (Algebra.TensorProduct.includeRight : C →ₐ[R] Rp ⊗[R] C).commutes r }
  let Φ : Rp ⊗[R] Cb →ₐ[Rp] Rp ⊗[R] C :=
    Algebra.TensorProduct.lift (Algebra.ofId Rp _) g (fun _ _ => Commute.all _ _)
  let Ψ : Rp ⊗[R] C →ₐ[Rp] Rp ⊗[R] Cb :=
    Algebra.TensorProduct.map (AlgHom.id Rp Rp) (IsScalarTower.toAlgHom R C Cb)
  have h1 : Φ.comp Ψ = AlgHom.id Rp _ := by
    ext c
    simp [Φ, Ψ, g, hg0]
  have h2 : Ψ.comp Φ = AlgHom.id Rp _ := by
    ext x
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change Ψ (Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x)) = (1 : Rp) ⊗ₜ[R] algebraMap C Cb x
    have : Φ ((1 : Rp) ⊗ₜ[R] algebraMap C Cb x) = (1 : Rp) ⊗ₜ[R] x := by
      simp [Φ, g, hg0]
    rw [this]
    simp [Ψ]
  exact Algebra.Etale.of_equiv (AlgEquiv.ofAlgHom Ψ Φ h2 h1).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocallyIffAffineEtalePointCover
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC


open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex in
theorem _root_.GlobalTheory.EtC.loc_iff_etale_affine_points : ∀ (U : Scheme.{0})
    (P : ∀ V : Scheme.{0}, (V ⟶ U) → Prop),
    (∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V), P V g → P W (k ≫ g)) →
    (_root_.GlobalTheory.EtC.Loc U P ↔ ∀ x : U, ∃ (V : Scheme.{0}) (g : V ⟶ U),
      IsAffine V ∧ Etale g ∧ x ∈ Set.range g ∧ P V g) := by
  intro U P hP
  unfold _root_.GlobalTheory.EtC.Loc
  constructor
  · rintro ⟨S, hS, hSP⟩ x
    obtain ⟨𝒰, h𝒰⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    haveI : Scheme.JointlySurjective (Scheme.precoverage (@Etale : MorphismProperty Scheme.{0})) :=
      Scheme.instJointlySurjectivePrecoverage
    obtain ⟨i, y, rfl⟩ := 𝒰.exists_eq x
    let A := (𝒰.X i).affineCover
    obtain ⟨z, hz⟩ := A.covers y
    have hE : Etale (𝒰.f i) := 𝒰.map_prop i
    refine ⟨A.X (A.idx y), A.f (A.idx y) ≫ 𝒰.f i, inferInstance, inferInstance, ⟨z, ?_⟩, ?_⟩
    · rw [Scheme.Hom.comp_apply, hz]
    · exact hSP _ _ (S.downward_closed (h𝒰 _ _ (Presieve.ofArrows.mk i)) _)
  · intro h
    choose V g hV hE hx hPg using h
    let S : Sieve U :=
      { arrows := fun W f => P W f, downward_closed := fun hf k => hP _ _ _ k hf }
    refine ⟨S, ?_, fun W f hf => hf⟩
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V g (fun x => ?_) (fun x => hE x), ?_⟩
    · obtain ⟨y, hy⟩ := hx x
      exact ⟨x, y, hy⟩
    · rintro _ _ ⟨x⟩
      exact hPg x

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMemIffPoints
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem etale_mem_iff_points : ∀ (U : Scheme.{0}) (S : Sieve U), S ∈ Scheme.etaleTopology.{0} U ↔
    ∀ u : U, ∃ (V : Scheme.{0}) (j : V ⟶ U) (v : V), Etale j ∧ j v = u ∧ S.arrows j := by
  intro U S
  constructor
  · intro hS u
    obtain ⟨𝒰, hle⟩ := (Scheme.mem_grothendieckTopology_iff (P := @Etale)).1 hS
    obtain ⟨i, v, hv⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).1 𝒰.mem₀).1 u
    exact ⟨𝒰.X i, 𝒰.f i, v, 𝒰.map_prop i, hv, hle _ _ (Presieve.ofArrows.mk i)⟩
  · intro h
    choose V j v hj hv hS using h
    refine (Scheme.mem_grothendieckTopology_iff (P := @Etale)).2
      ⟨Scheme.Cover.mkOfCovers U V j (fun u => ⟨u, v u, hv u⟩) hj, ?_⟩
    intro W f hf
    obtain ⟨u⟩ := hf
    exact hS u

end GlobalTheory
end

