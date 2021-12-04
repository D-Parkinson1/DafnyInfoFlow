﻿using Microsoft.Dafny.LanguageServer.Util;
using OmniSharp.Extensions.LanguageServer.Protocol.Document;
using OmniSharp.Extensions.LanguageServer.Protocol.Models;
using OmniSharp.Extensions.LanguageServer.Protocol.Server;
using System.Collections.Generic;
using System.Linq;

namespace Microsoft.Dafny.LanguageServer.Language {
  public class DiagnosticPublisher : IDiagnosticPublisher {
    private readonly ILanguageServerFacade _languageServer;

    public DiagnosticPublisher(ILanguageServerFacade languageServer) {
      _languageServer = languageServer;
    }

    public void PublishDiagnostics(DafnyDocument document) {
      _languageServer.TextDocument.PublishDiagnostics(ToPublishDiagnostics(document));
    }

    public void HideDiagnostics(DafnyDocument document) {
      _languageServer.TextDocument.PublishDiagnostics(new PublishDiagnosticsParams {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = new Container<Diagnostic>()
      });
    }

    private static PublishDiagnosticsParams ToPublishDiagnostics(DafnyDocument document) {
      return new() {
        Uri = document.Uri,
        Version = document.Version,
        Diagnostics = ToDiagnostics(document).ToArray(),
      };
    }

    private static IEnumerable<Diagnostic> ToDiagnostics(DafnyDocument document) {
      // Only report errors of the entry-document.
      if (document.Errors.Diagnostics.TryGetValue(document.GetFilePath(), out var diagnostics)) {
        return diagnostics;
      }
      return Enumerable.Empty<Diagnostic>();
    }
  }
}
