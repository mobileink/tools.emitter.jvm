;;   Copyright (c) Nicola Mometto, Rich Hickey & contributors.
;;   The use and distribution terms for this software are covered by the
;;   Eclipse Public License 1.0 (http://opensource.org/licenses/eclipse-1.0.php)
;;   which can be found in the file epl-v10.html at the root of this distribution.
;;   By using this software in any fashion, you are agreeing to be bound by
;;   the terms of this license.
;;   You must not remove this notice, or any other, from this software.

(ns clojure.tools.emitter.xml
  (:refer-clojure :exclude [eval macroexpand-1 macroexpand load])
  (:require [clojure.tools.analyzer.jvm :as a]
            [clojure.tools.analyzer :refer [macroexpand-1 macroexpand]]
            [clojure.tools.analyzer.passes :refer [schedule]]
            [clojure.tools.analyzer.env :as env]
            [clojure.tools.analyzer.utils :refer [mmerge]]
            [clojure.tools.emitter.xml.emit :as e]
            ;; [clojure.tools.emitter.jvm.transform :as t]
            [clojure.tools.emitter.xml.transform :as x]
            [clojure.tools.analyzer.passes
             [collect-closed-overs :refer [collect-closed-overs]]
             [trim :refer [trim]]]
            [clojure.tools.emitter.passes.jvm
             [collect :refer [collect]]
             [collect-internal-methods :refer :all]
             [clear-locals :refer [clear-locals]]
             [annotate-class-id :refer [annotate-class-id]]
             [annotate-internal-name :refer [annotate-internal-name]]
             [ensure-tag :refer [ensure-tag]]]
            [clojure.java.io :as io]
            [clojure.string :as s]
            [clojure.pprint :as pp]
            [clojure.tools.reader :as r]
            [clojure.tools.reader.reader-types :as readers]
            [clojure.data.xml :as xml])
  (:import [clojure.lang IFn DynamicClassLoader Atom]
           [java.io ByteArrayInputStream PrintWriter Reader StringReader StringWriter]
           [java.nio.file Files Paths StandardOpenOption]
           [java.nio.charset Charset StandardCharsets]
           [javax.xml.stream XMLInputFactory
                             XMLStreamReader
                             XMLStreamConstants]
           [javax.xml.parsers DocumentBuilder DocumentBuilderFactory]
           [javax.xml.transform.dom DOMSource]
           [javax.xml.transform OutputKeys TransformerFactory]
           [javax.xml.transform.stream StreamSource StreamResult]))

(defn write-class
  "(λ ClassName → Bytecode) → Nil

  Writes the given bytecode to a file named by the ClassName and
  *compile-path*. Requires that *compile-path* be set. Returns Nil."
  [name bytecode]
  {:pre [(bound? #'clojure.core/*compile-path*)]}
  (println "*COMPILE-PATH*: " *compile-path*)
  (let [path (str *compile-path* "/" name ".class")
        file (io/file path)]
    (.mkdirs (io/file (.getParent file)))
    (with-open [w (java.io.FileOutputStream. path)]
      (.write w bytecode)))
  nil)

(defn write-xml
  "Writes the given xml to a file named by the ClassName and
  *compile-path*. Requires that *compile-path* be set. Returns Nil."
  [name xml]
  {:pre [(bound? #'clojure.core/*compile-path*)]}
  (let [opath (str *compile-path* "/" name ".xml")
        file (io/file opath)]
    (.mkdirs (io/file (.getParent file)))
    (with-open [outfile (java.io.FileWriter. opath)]
      (spit outfile xml)))
      ;; (xml/emit xml outfile)))
    ;; (with-open [w (java.io.FileOutputStream. path)]
    ;;   (.write w bytecode)))
  nil)

(declare pprint-xml)

(defn compile-and-load
  ;; ([class-ast]
  ;;    (compile-and-load class-ast (clojure.lang.RT/makeClassLoader)))
  ([{:keys [class-name] :as xml}] ;; class-loader]
   (let [xml-str (pprint-xml xml)]
  (println "compile-and-load:" xml-str)
   ;; (let [;;bytecode (x/-compile class-ast)
   ;;       xcode class-ast]
       (when (and (bound? #'clojure.core/*compile-files*)
                  *compile-files*)
         (write-xml
          ;;class-name
          "test"
          xml-str)))))

(def passes (into (disj a/default-passes #'trim)
                  #{}
                  #_#{#'collect-internal-methods

                    #'ensure-tag

                    #'annotate-class-id
                    #'annotate-internal-name

                    #'collect
                    #'collect-closed-overs
                    #'clear-locals}))

(def run-passes
  (schedule passes))

(defn eval
  "(eval form)
   (eval form eval-options-map)

  Form is a read Clojure s expression represented as a list.
  Eval-options-map is a map, defaulting to the empty map, the
  following values of which are significant. Returns the result of
  evaling the input expression.

  Options
  -----------
  :debug? :- (Option Bool)
    Enables or disables printing in eval. Used as the default value for
    printing in the emitter.

  :emit-opts :- (Option emit-options-map)
    An options map which will be merged with the default options
    provided to emit. Keys in this map take precidence over the default
    values provided to emit. The keys which are significant in this map
    are documented in the t.e.jvm.emit/emit docstring.

  :analyze-opts :- (Option analyze-options-map)
    An options map that will be passed to the analyzer. The keys which
    are significant in this map are documented in the t.a.jvm/analyze
    docstring.

  :class-loader :- (Option ClassLoader)
    An optional classloader into which compiled functions will be
    injected. If not provided, a new Clojure classloader will be
    used. If a class loader is provided here, one need not be provided
    in eval-opts.

  :compile-files :- (Option Bool)
    Enables or disables writing classfiles for generated classes. False
    by default."

  ([form]
     (eval form {}))
  ([form {:keys [debug? emit-opts class-loader analyze-opts compile-files]
          :or {debug?        false
               emit-opts     {}
               analyze-opts  a/default-passes-opts
               compile-files (if (bound? #'clojure.core/*compile-files*)
                               *compile-files* false)
               ;; class-loader  (clojure.lang.RT/makeClassLoader)
               }
          :as options}]
     ;;{:pre [(instance? DynamicClassLoader class-loader)]}
   ;; if *expand-macros*...
     ;; (let [mform (binding [macroexpand-1 a/macroexpand-1]
     (let [mform (binding [macroexpand-1 a/macroexpand-0]
                   (macroexpand form (a/empty-env)))]
       (if (and (seq? mform) (= 'do (first mform)))
         (let [[statements ret] (loop [statements [] [e & exprs] (rest mform)]
                                  (if (seq exprs)
                                    (recur (conj statements e) exprs)
                                    [statements e]))]
           (doseq [expr statements]
             (eval expr options))
           (eval ret options))
         (binding [a/run-passes    run-passes
                   *compile-files* compile-files]
           ;; :once marks fn as run-once only
           ;;(let [clj-ast (a/analyze `(^:once fn* [] ~mform) (a/empty-env) analyze-opts)
            (let [clj-ast (a/analyze mform (a/empty-env) analyze-opts)
                 _ (println "CLJ AST: ")
                 _ (pp/pprint clj-ast)
                 cs (e/emit-xml clj-ast (merge {:debug? debug?} emit-opts))
                 _ (println "JVM AST type: " (type cs))
                 ;; classes (mapv #(compile-and-load %
                 ;;                                  ;; class-loader
                 ;;                                  )
                 ;;               ;;clj-ast)
                 ;;               cs)
                 ]
              (compile-and-load cs)
             #_(print "CLASSES: " (last classes))
             #_((.newInstance ^Class (last classes)))))))))

(def root-directory @#'clojure.core/root-directory)

(defn load
  "(load resource)
   (load resource load-options-map)

  Resource is a string identifier for a Clojure resource on the
  classpath. Load-options is a a map, defalting to the empty map, in
  which the following keys are meaningful. Returns nil.

  Options
  -----------
  :debug? :- (Option Bool)
    Enables or disables printing in eval. Used as the default value for
    printing in the emitter.

  :eval-opts  :- (Option eval-options-map)
    An options map which will be merged with the default options
    provided to eval. Keys set in this map take precidence over the
    default values supplied to eval. The keys which are significant in
    this map are documented in the t.e.jvm/eval docstring.

  :class-loader :- (Option ClassLoader)
    An optional classloader into which compiled functions will be
    injected. If not provided, a new Clojure classloader will be
    used. If a class loader is provided here, one need not be provided
    in eval-opts.

  :compile-files :- (Option Bool)
    Enables or disables writing classfiles for generated classes. False
    by default."

  ([res]
     (load res {}))
  ([res {:keys [debug? eval-opts class-loader compile-files]
         :or   {debug?        false
                eval-opts     {}
                compile-files (if (bound? #'clojure.core/*compile-files*)
                                *compile-files* false)
                class-loader  (clojure.lang.RT/makeClassLoader)}
         :as options}]
     (let [p      (str (apply str (replace {\. \/ \- \_} res)) ".clj")
           eof    (Object.)
           p      (if (.startsWith p "/")
                    (subs p 1)
                    (subs (str (root-directory (ns-name *ns*)) "/" p) 1))
           file   (-> p io/resource io/reader slurp)
           reader (readers/indexing-push-back-reader file 1 p)]
       (binding [*ns*            *ns*
                 *file*          p
                 *compile-files* compile-files]
         (loop []
           (let [form (r/read reader false eof)]
             (when (not= eof form)
               (eval form (merge eval-opts
                                 (when class-loader
                                   {:class-loader  class-loader
                                    :compile-files compile-files})))
               (recur))))
         nil))))

(xml/alias-uri 'jvm "http://clojure.org/tools/emitter/jvm")

(defn pprint-xml
  [& elts]
  ;; (log/info "PPRINT-IMPL: " elts)
  (let [s elts #_(if (or (= :html (first elts))
                  (= :xml (first elts)))
            (do ;(log/trace "FIRST ELT: " (first elts) " " (keyword? (first elts)))
                (rest elts))
            (if (keyword? (first elts))
              (throw (Exception. "only :html and :xml supported"))
              elts))
        ;; fmt (if (keyword? (first elts)) (first elts) :html)
        ;; void (reset! mode fmt)
        ;; log (log/trace "mode: " @mode)
        ;; always serialize to xml, deal with html issues in the transform
        ml (if (string? s)
             (throw (Exception. "xml pprint only works on miraj.co-dom.Element"))
             (xml/emit-str elts)
             #_(if (> (count s) 3)
               (do ;;(println "pprint-impl FOREST")
                   (let [s (serialize-raw :xml (element :CODOM_56477342333109 s))]
                     (reset! mode fmt)
                     s))
               (let [s (serialize-raw :xml s)]
                 ;; (reset! mode fmt)
                 s)))
        ;; _ (log/info "XML PPRINT SERIALIZED: " ml)
        xmlSource (StreamSource.  (StringReader. ml))
        xmlOutput (StreamResult.
                   (let [sw (StringWriter.)]
                     #_(if (.startsWith ml "<!doctype")
                       (.write sw "<!doctype html>\n"))
                     sw))
        factory (TransformerFactory/newInstance)

        ;; _ (log/debug (format "XSL-ID-X %s" xsl-identity-transform-html))
        transformer #_(if (= :html @mode)
                      (let [r (io/resource "miraj/co_dom/identity-html.xsl")
                            xsl (slurp r)]
                        ;; (StringReader. xsl-identity-transform-html))))
                        (.newTransformer factory (StreamSource. (StringReader. xsl))))
                      (let [r (io/resource "miraj/co_dom/identity-xml.xsl")
                            xsl (slurp r)]
                        ;;(log/trace "transforming with xsl-identity-transform-xml")
                        (.newTransformer factory (StreamSource. (StringReader. xsl)))))
        (let [;;r (io/resource "xsl/identity-xml.xsl")
              xsl (slurp "xsl/identity-xml.xsl")]
          ;;(log/trace "transforming with xsl-identity-transform-xml")
          (.newTransformer factory (StreamSource. (StringReader. xsl))))]
    (.setOutputProperty transformer OutputKeys/METHOD "xml")
    (.setOutputProperty transformer OutputKeys/STANDALONE "yes")
    (.setOutputProperty transformer OutputKeys/ENCODING "utf-8")
    (.setOutputProperty transformer OutputKeys/INDENT "yes")
    (.setOutputProperty transformer "{http://xml.apache.org/xslt}indent-amount", "4")
    #_(if (.startsWith ml "<?xml")
      (.setOutputProperty transformer OutputKeys/OMIT_XML_DECLARATION "no")
      (.setOutputProperty transformer OutputKeys/OMIT_XML_DECLARATION "yes"))

    (.transform transformer xmlSource xmlOutput)
    (let[result #_(if (= :html fmt)
                  (let [string-writer (.getWriter xmlOutput)
                        s (.toString string-writer)
                        ;; _ (prn "XML OUTPUT: " s)
                        void (.flush string-writer)
                        ]
                    ;;(str/replace s regx "")
                    s)
                  (do (println "XML FOOBAR")
                      (.toString (.getWriter xmlOutput))))
         (do (println "XML FOOBAR")
             (.toString (.getWriter xmlOutput)))]
      ;; (prn "PPRINT OUTPUT: " result)
      result)))
