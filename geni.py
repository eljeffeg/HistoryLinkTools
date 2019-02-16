#!/usr/bin/env python
#
# Copyright 2012-2019 Jeff Gentes
#

#Python client library for the Geni Platform.

import urllib
import urllib2
import re
import logging
import time
import sys
import MultipartPostHandler
import traceback
from collections import Iterable
from datetime import date

logging.basicConfig(format='%(asctime)s,%(msecs)d %(levelname)-8s [%(filename)s:%(lineno)d] %(message)s',
    datefmt='%d-%m-%Y:%H:%M:%S',
    level=logging.DEBUG)

# Find a JSON parser
try:
    import simplejson as json
except ImportError:
    try:
        from django.utils import simplejson as json
    except ImportError:
        import json
_parse_json = json.loads

# Find a query string parser
try:
    from urlparse import parse_qs
except ImportError:
    from cgi import parse_qs


class GeniAPI(object):

    def __init__(self, access_token=None, refresh_token=None, options=None):
        self.access_token = access_token
        self.refresh_token = refresh_token
        self.options = options

    # based on: http://code.activestate.com/recipes/146306/
    def _encode_multipart_form(self, fields):
        """Fields are a dict of form name-> value
        For files, value should be a file object.
        Other file-like objects might work and a fake name will be chosen.
        Return (content_type, body) ready for httplib.HTTP instance
        """
        BOUNDARY = '----------ThIs_Is_tHe_bouNdaRY_$'
        CRLF = '\r\n'
        L = []
        for (key, value) in fields.items():
            logging.debug("Encoding %s, (%s)%s" % (key, type(value), value))
            if not value:
                continue
            L.append('--' + BOUNDARY)
            if hasattr(value, 'read') and callable(value.read):
                filename = getattr(value, 'name', '%s.jpg' % key)
                L.append(('Content-Disposition: form-data;'
                          'name="%s";'
                          'filename="%s"') % (key, filename))
                L.append('Content-Type: image/jpeg')
                value = value.read()
                logging.debug(type(value))
            else:
                L.append('Content-Disposition: form-data; name="%s"' % key)
            L.append('')
            if isinstance(value, unicode):
                logging.debug("Convert to ascii")
                value = value.encode('ascii')
            L.append(value)
        L.append('--' + BOUNDARY + '--')
        L.append('')
        body = CRLF.join(L)
        content_type = 'multipart/form-data; boundary=%s' % BOUNDARY
        return content_type, body

    def get_family(self, profile=None, siblings=True, parents=True, children=False, spouse=False):
        if not profile:
            profile = "profile"
        elif not str(profile).startswith("profile"):
            profile = "profile-" + profile
        args = {"fields": "id,name,gender,deleted"}
        request = self.request(profile + "/immediate-family", args)
        family = Family(profile, request, siblings=siblings, parents=parents, children=children, spouse=spouse)
        #family.print_family()
        return family

    def get_profile_detailed(self, profile=None):
        if not profile:
            profile = "profile"
        elif not str(profile).startswith("profile"):
            profile = "profile-" + profile
        args = {
            "fields": "id,guid,name,title,first_name,middle_name,last_name,maiden_name,suffix,display_name,nicknames,gender,deleted,birth,baptism,death,burial,cause_of_death,is_alive,occupation,photo_urls,marriage,divorce,locked_fields,match_counts",
            "actions": "update,update-basics,add"}
        response = self.request(profile, args)
        id = None
        name = None
        if "id" in response:
            id = response["id"]
        if "name" in response:
            name = response["name"]
        return Relative(id, name, "self", response)

    def get_family_detailed(self, profile=None, siblings=True, parents=True, children=False, spouse=False, focusprofile=False):
        if not profile:
            profile = "profile"
        elif not str(profile).startswith("profile"):
            profile = "profile-" + profile
        args = {
            "fields": "id,guid,name,title,first_name,middle_name,last_name,maiden_name,suffix,display_name,nicknames,gender,deleted,birth,baptism,death,burial,cause_of_death,is_alive,occupation,photo_urls,marriage,divorce,locked_fields,match_counts",
            "actions": "update,update-basics,add"}
        request = self.request(profile + "/immediate-family", args)
        family = Family(profile, request, siblings=siblings, parents=parents, children=children, spouse=spouse, focusprofile=focusprofile)
        #family.print_family()
        return family

    def process_group(self, family_group, siblings=True, parents=True, children=False, spouse=False):
        family_list = []
        if family_group and "results" in family_group:
            for item in family_group["results"]:
                family = Family("profile", item, siblings=siblings, parents=parents, children=children, spouse=spouse)
                family_list.append(family)
        elif family_group and "nodes" in family_group:
            family = Family("profile", family_group, siblings=siblings, parents=parents, children=children, spouse=spouse)
            family_list.append(family)
        else:
            if "error" in family_group:
                if "message" in family_group["error"]:
                    if "Access Denied" == family_group["error"]["message"]:
                        return family_list
                    elif "Invalid access token" == family_group["error"]["message"]:
                        return "Invalid access token"
            logging.warning("**** No results ****")
            logging.warning(family_group)
        return family_list

    def get_family_group(self, family_root, siblings=True, parents=True, children=False, spouse=False):
        query = "profile/immediate-family"
        ids = ""
        result = []
        if not isinstance(family_root, (list, tuple)):
            family_root = [family_root]
        while len(family_root) > 0:
            ids += family_root.pop() + ","
        ids = ids[:-1]
        extraargs = ""
        if not siblings:
            extraargs = ",claimed,birth,death"
        args = {"ids": ids, "fields": "id,name,gender,master_profile,merge_pending,public,living,deleted,project_ids" + extraargs}
        family_group = self.request(query, args)
        if "error" not in family_group:
            result = self.process_group(family_group, siblings=siblings, parents=parents, children=children, spouse=spouse)
        else:
            if "message" in family_group["error"]:
                if "Invalid access token" == family_group["error"]["message"]:
                    result = ["Invalid access token"]
                elif "Access Denied" == family_group["error"]["message"]:
                    newlist = []
                    startlist = ids.split(",")
                    if len(startlist) == 1:
                        relative = self.get_profile(startlist[0])
                        if "public" in relative:
                            if not relative["public"]:
                                return [Family("profile", relative, siblings=siblings, parents=parents, children=children, spouse=spouse, error="Access Denied")]
                            else:
                                return []
                        else:
                            return []
                    idlist = [startlist[i::2] for i in range(2)]
                    for family_root in idlist:
                        newlist.extend(self.get_family_group(family_root, siblings=siblings, parents=parents, children=children, spouse=spouse))
                    result = newlist
        return result

    def get_parents(self, profile):
        family = self.get_family(profile, siblings=False)
        return family.get_parents()

    def get_family_parents(self, profile):
        family = self.get_direct_parents(profile)
        return family

    def get_family_children(self, profile):
        family = self.get_direct_children(profile)
        return family

    def get_direct_parents(self, family_root):
        unions = self.get_unions(family_root, siblings=False, parents=True, children=False, spouse=False)
        return unions

    def get_direct_children(self, family_root):
        unions = self.get_unions(family_root, siblings=False, parents=False, children=True, spouse=False)
        return unions

    def get_unions(self, family_root, siblings=True, parents=True, children=False, spouse=False):
        fields = "id,union,living,deleted"
        query = "profile/immediate-family"
        family_group = self.group_query(family_root, query, fields)
        result = self.process_group(family_group, siblings=siblings, parents=parents, children=children, spouse=spouse)
        if isinstance(result, str):
            return result
        result = self.process_unions(result)
        return result

    def update_relative(self, relative):
        fields = "id,name,gender,master_profile,merge_pending,public,claimed,birth,death,living"
        query = "profile"
        results = self.group_query(relative.get_id(), query, fields)
        relative.update(results)
        return relative

    def process_unions(self, family_group):
        allids = []
        allrelatives = {}
        for family in family_group:
            for item in family.family:
                if item.get_id() in allrelatives:
                    allrelatives[item.get_id()].append(item)
                else:
                    allrelatives[item.get_id()] = [item]
                    allids.append(item.get_id())

        if len(allids) > 0:
            fields = "id,name,gender,master_profile,merge_pending,public,claimed,birth,death,living"
            query = "profile"
            idchunks = self.chunks(allids, 35)
            for idgroup in idchunks:
                union_results = self.group_query(idgroup, query, fields)
                if "results" in union_results:
                    for item in union_results["results"]:
                        for relative in allrelatives[item["id"]]:
                            relative.update(item)
                elif "name" in union_results:
                    item = union_results
                    for relative in allrelatives[item["id"]]:
                        relative.update(item)
            return family_group
        return []

    def group_query(self, family_root, query, fields):
        ids = ""
        if isinstance(family_root, (list, tuple)):
            while len(family_root) > 0:
                ids += family_root.pop() + ","
            ids = ids[:-1]
        else:
            ids = family_root
        ids = ids.replace("profile-", "")
        args = {"ids": ids, "fields": fields, "only_ids": "true"}
        return self.request(query, args)

    def get_children(self, profile):
        family = self.get_family(profile)
        return family.get_children()

    def get_spouse(self, profile):
        family = self.get_family(profile)
        return family.get_spouse()

    def get_siblings(self, profile):
        family = self.get_family(profile)
        return family.get_siblings()

    def get_master(self, profiles):
        path = ""
        for profile in profiles:
            path += profile + ","
        path = path[:-1]
        args = {"id": path, "fields": "id,name,master_profile"}
        result = self.request("profile", args)
        match = []
        try:
            for item in result:
                for profile in result[item]:
                    if "master_profile" in profile:
                        match.append({"id": profile["id"], "name": profile["name"]})
        except:
            pass
        return match

    def get_project(self, project, path=None, args=None):
        if not str(project).startswith("project"):
            project = "project-" + project
        if path:
            project += "/" + path
        return self.request(project, args)

    def get_projects(self, projects):
        query = "project"
        ids = ""
        resultlist = []
        if isinstance(projects, (list, tuple)):
            while len(projects) > 0:
                idval = int(projects.pop())
                if idval in self.options.historycache:
                    resultlist.append({'id': idval, 'name': self.options.historycache[idval]})
                else:
                    ids += str(idval) + ","
            if len(ids) > 0:
                ids = ids[:-1]
        else:
            idval = int(projects)
            if idval in self.options.historycache:
                resultlist.append({'id': idval, 'name': self.options.historycache[idval]})
            else:
                ids = projects
        if len(ids) > 0:
            ids = ids.replace("project-", "")
            fields = "id,name"
            args = {"ids": ids, "fields": fields}
            results = self.request(query, args)
            if "results" in results:
                results = results["results"]
                for item in results:
                    idval = int(item["id"].replace("project-", ""))
                    self.options.historycache[idval] = item["name"]
                    resultlist.append({'id': idval, 'name': item["name"]})
            else:
                results["id"] = results["id"].replace("project-", "")
                idval = int(results["id"].replace("project-", ""))
                self.options.historycache[idval] = results["name"]
                resultlist.append({'id': idval, 'name': results["name"]})
        return resultlist

    def get_profile(self, profile, path=None, args=None):
        if not str(profile).startswith("profile"):
            profile = "profile-" + profile
        if path:
            profile += "/" + path
        return self.request(profile, args)

    def get_project_name(self, project):
        args = {'fields': 'name'}
        name = self.get_project(project, None, args)
        if "name" in name:
            return name["name"]
        return name

    def get_profile_name(self, profile):
        args = {'fields': 'name'}
        name = self.get_profile(profile, None, args)
        if "name" in name:
            return name["name"]
        return name

    def get_profile_info(self, profile):
        args = {'fields': 'name,id,gender'}
        info = self.get_profile(profile, None, args)
        return info

    def get_project_profiles(self, project):
        args = {'fields': 'id,name'}
        proj = Project(self, project, self.get_project(project, "profiles", args))
        return proj.get_results()

    def get_project_collaborators(self, project):
        args = {'fields': 'id'}
        proj = Project(self, project, self.get_project(project, "collaborators", args))
        return proj.get_results()

    def get_project_followers(self, project):
        args = {'fields': 'id'}
        proj = Project(self, project, self.get_project(project, "followers", args))
        return proj.get_results()

    def follow_profile(self, profile):
        post_args = {'fields': 'id'}
        return self.request(profile+"/follow", None, post_args)

    def unfollow_profile(self, profile):
        post_args = {'fields': 'id'}
        return self.request(profile+"/unfollow", None, post_args)

    def chunks(self, l, n):
        return [l[i:i+n] for i in range(0, len(l), n)]

    def get_refresh_token(self):
        if self.refresh_token:
            refresh = "https://www.geni.com/platform/oauth/request_token?" + urllib.urlencode({
                "refresh_token": self.refresh_token,
                "grant_type": "refresh_token",
                "client_id": self.options.geni_app_id,
                "client_secret": self.options.geni_app_secret,
                })
            response = urllib.urlopen(refresh)
            redata = response.read()
            if "error" in redata:
                return
            else:
                mytoken = json.loads(redata)
                self.access_token = mytoken["access_token"]
                self.refresh_token = mytoken["refresh_token"]

    def request(self, path, args=None, post_args=None, post_data=None):
        """Fetches the given path in the Geni API.

        We translate args to a valid query string. If post_args is given,
        we send a POST request to the given path with the given arguments.
        """
        args = args or {}
        response = ""
        if self.access_token:
            if post_args is not None:
                post_args["access_token"] = self.access_token
            else:
                args["access_token"] = self.access_token
        if not post_data and post_args:
            post_data = urllib.urlencode(post_args)
        try:
            url = "https://www.geni.com/api/" + path + "?" + urllib.urlencode(args)
            if post_data and "file" in post_data:
                opener = urllib2.build_opener(MultipartPostHandler.MultipartPostHandler)
                file = opener.open(url, post_data)
            else:
                file = urllib2.urlopen(url, post_data)
        except urllib2.HTTPError, e:
            try:
                response = _parse_json(e.read())
            except:
                response = sys.exc_info()[0]
            if not isinstance(response, Iterable):
                if post_data:
                    logging.warning("****** Error with photo upload ******")
                else:
                    logging.warning("****** Error with Geni Response ******")
                logging.warning(e.read())
                if response:
                    logging.info("****** Error: " + url + " ******")
                    logging.warning(response)
                #traceback.print_exc()
                file = None
            else:
                try:
                    if response and "error" in response and "message" in response["error"]:
                        message = response["error"]["message"]
                        if "Rate limit exceeded." == message:
                            i = 3 #Try it 3 times
                            while message == "Rate limit exceeded." and i > 0:
                                time.sleep(3)
                                i -= 1
                                try:
                                    file = urllib2.urlopen("https://www.geni.com/api/" + path + "?" +
                                                           urllib.urlencode(args), post_data)
                                    message = "Pass"
                                except:
                                    response = _parse_json(e.read())
                                    if "error" in response and "message" in response["error"]:
                                        message = response["error"]["message"]
                                    else:
                                        message = "error"
                                        logging.warning("***** Error: " + path + "?" + urllib.urlencode(args) + " *****")
                                        logging.warning(response)
                                    file = None
                        elif "Access Denied" == message:
                            file = None
                        else:
                            logging.warning("****** Error: " + path + "?" + urllib.urlencode(args) + " ******")
                            logging.warning(response)
                            file = None
                    else:
                        logging.warning("****** Error: " + path + "?" + urllib.urlencode(args) + " ******")
                        logging.warning("Problem with response - None")
                        file = None
                except:
                    try:
                        logging.warning("****** Error: " + path + "?" + urllib.urlencode(args) + " ******")
                        logging.warning(response)
                        traceback.print_exc()
                    except:
                        logging.warning("****** Error: " + path + "?" + urllib.urlencode(args) + " ******")
                        logging.warning("Problem with response - Exception")
                        traceback.print_exc()
                    file = None
        try:
            if file:
                fileInfo = file.info()
                if fileInfo.maintype == 'text':
                    response = _parse_json(file.read())
                elif fileInfo.maintype == 'application':
                    response = _parse_json(file.read())
                elif fileInfo.maintype == 'image':
                    mimetype = fileInfo['content-type']
                    response = {
                        "data": file.read(),
                        "mime-type": mimetype,
                        "url": file.url,
                        }
                else:
                    logging.warning('Maintype was not text or image')
        except:
            logging.warning("****** " + path + "?" + urllib.urlencode(args) + " ******")
            logging.warning("Problem with response - Exception")
            logging.warning(file.read())
        finally:
            if file:
                file.close()
        return response


class Project(object):
    def __init__(self, api, focus, response):
        self.api = api
        self.focus = focus
        self.response = response
        self.profiles = []
        next = "start"
        while next:
            next = self.process_response()

    def get_json(self):
        return self.response

    def get_results(self):
        return self.profiles

    def process_response(self):
        next = None
        if not 'results' in self.response and "id" in self.response:
            xitem = self.response
            name = "(No Name)"
            if "name" in xitem:
                name = xitem["name"]
            self.profiles.append({"id": xitem["id"], "name": name})
            return next

        for item in self.response:
            if item == 'next_page':
                try:
                    next = self.response[item]
                except:
                    pass
            if item == 'results':
                for xitem in self.response[item]:
                    try:
                        name = "(No Name)"
                        if "name" in xitem:
                            name = xitem["name"]
                        self.profiles.append({"id": xitem["id"], "name": name})
                    except:
                        pass

        if next:
            try:
                file = urllib2.urlopen(next)
                self.response = _parse_json(file.read())
            except:
                logging.warning("Problem getting (trying again): " + next)
                try:
                    self.api.get_refresh_token()
                    next = re.sub(r'access_token.*?&', 'access_token=' + self.api.access_token + "&", next)
                    file = urllib2.urlopen(next)
                    self.response = _parse_json(file.read())
                except:
                    logging.warning("Problem getting (failed - skipping): " + next)
                    traceback.print_exc()
                    self.response = None
                    next = None
        return next


class Family(object):
    def __init__(self, focus, response, siblings=True, parents=True, children=False, spouse=False, focusprofile=False, error=None):
        self.unions = []
        self.family = []
        self.person = None
        if error:
            profile = None
            name = None
            if "id" in response:
                profile = response["id"]
            if "name" in response:
                name = response["name"]
            if profile:
                relative = Relative(profile, name, "unknown", response, message=error)
                if relative:
                    self.family.append(relative)
            else:
                logging.warning('No id? ' + response)
        else:
            if "profile" == focus:
                if "name" in response["focus"] and "gender" in response["focus"]:
                    self.person = Relative(response["focus"]["id"], response["focus"]["name"], self.self_relation(response["focus"]["gender"]), response["focus"])
                else:
                    self.person = Relative(response["focus"]["id"], "Unknown", "father", response["focus"])
            else:
                self.person = Relative(focus, "Unknown", "father", response)
            if not "nodes" in response:
                return
            for item in response["nodes"]:
                if str(item).startswith("union"):
                    union = Union(str(item), response["nodes"][item])
                    if union:
                        self.unions.append(union)

            for item in response["nodes"]:
                if str(item).startswith("profile"):
                    deleted = None
                    if "deleted" in response["nodes"][item]:
                        deleted = response["nodes"][item]["deleted"]
                    if deleted:
                        continue
                    if "gender" in response["nodes"][item]:
                        gender = response["nodes"][item]["gender"]
                    else:
                        gender = "Unknown"
                    name = None

                    if "name" in response["nodes"][item]:
                        name = response["nodes"][item]["name"]
                    for edge in response["nodes"][item]["edges"]:
                        rel = response["nodes"][item]["edges"][edge]["rel"]
                        relative = self.process_unions(edge, item, rel, gender, name, response["nodes"][item])
                        if relative:
                            relation = relative.get_rel(0)
                            if focusprofile and relation == "focus":
                                self.family.append(relative)
                            if parents and (relation == "parent" or relation == "mother" or relation == "father"):
                                self.family.append(relative)
                            if siblings and (relation == "sibling" or relation == "brother" or relation == "sister"):
                                self.family.append(relative)
                            if children and (relation == "child" or relation == "son" or relation == "daughter"):
                                self.family.append(relative)
                            if spouse and (relation == "spouse" or relation == "wife" or relation == "husband" or relation == "partner"):
                                self.family.append(relative)

    def self_relation(self, gender="male"):
        if gender == "male":
            return "father"
        else:
            return "mother"

    def get_person(self):
        return self.person

    def get_focus(self):
        if not self.person:
            return None
        return self.person.get_id()

    def get_name(self):
        return self.person.get_name()

    def get_rel(self, gen=1):
        return self.person.get_rel(gen)

    def get_profile(self, profile, gen=0):
        relative = None
        name = None
        if "id" in profile:
            name = profile["name"]
            profile = profile["id"]
        for item in self.family:
            if item.get_id() == profile:
                relative = item
                break
        if name:
            relative_profile = {"id": relative.get_id(), "relation": relative.get_rel(gen), "name": name}
        else:
            relative_profile = {"id": relative.get_id(), "relation": relative.get_rel(gen)}
        return relative_profile

    def get_family_all(self):
        relatives = []
        for item in self.family:
            relatives.append(item.get_id())
        return relatives

    def get_family_all_info(self):
        relatives = []
        for item in self.family:
            relatives.append(item.get_full_info(adopt=True))
        return relatives

    def get_family_branch_group(self):
        relatives = []
        for relative in self.family:
            rel = relative.get_rel()
            id = None
            if rel == "parent" or rel == "father" or rel == "mother":
                id = relative.get_id()
            elif rel == "sibling" or rel == "sister" or rel == "brother":
                id = relative.get_id()
            elif relative.get_message():
                id = relative.get_id()
            if id:
                relatives.append(relative)
        return relatives

    def get_family_branch(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "parent" or rel == "father" or rel == "mother":
                relatives.append(item.get_id())
            elif rel == "sibling" or rel == "aunt" or rel == "uncle":
                relatives.append(item.get_id())
        return relatives

    def get_parents(self, adopt=1):
        relatives = []
        adopted = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "father" or rel == "mother" or rel == "parent":
                if adopt == 1:
                    relatives.append(item)
                elif not item.is_adopted():
                    relatives.append(item)
                else:
                    adopted.append(item)
        if adopt == 3 and len(adopted) > 0:
            relatives = adopted
        elif len(relatives) == 0 and len(adopted) > 0:
            relatives.extend(adopted)
        return relatives

    def get_parents_info(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "father" or rel == "mother" or rel == "parent":
                relatives.append(item.get_info())
        return relatives

    def get_siblings(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "brother" or rel == "sister" or rel == "sibling":
                relatives.append(item)
        return relatives

    def get_siblings_info(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "brother" or rel == "sister" or rel == "sibling":
                relatives.append(item.get_info())
        return relatives

    def get_children(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "son" or rel == "daughter" or rel == "child":
                relatives.append(item)
        return relatives

    def get_children_info(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "son" or rel == "daughter" or rel == "child":
                relatives.append(item.get_info())
        return relatives

    def get_spouse(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "wife" or rel == "husband" or rel == "spouse" or rel == "partner":
                relatives.append(item)
        return relatives

    def get_spouse_info(self):
        relatives = []
        for item in self.family:
            rel = item.get_rel()
            if rel == "wife" or rel == "husband" or rel == "spouse" or rel == "partner":
                relatives.append(item.get_info())
        return relatives

    def print_family(self):
        logging.info("\nFocus: " + self.person.get_id())
        for relative in self.family:
            logging.info("\t" + relative.get_id() + ", " + relative.get_rel())
        logging.info("\n")

    def process_unions(self, union, profile, rel, gender, name, response):
        for item in self.unions:
            if union == item.get_id():
                return item.get_edge(profile, self.person.get_id(), rel, gender, name, response)


class Relative(object):
    def __init__(self, id, name, relation, response, union="", status="", message=False, adopt=False):
        self.relation = relation
        self.name = name
        self.message = message
        self.adopted = adopt
        self.id = id
        self.union = union
        self.status = status
        self.response = response
        self.update(response)

    def update(self, response):
        self.master = False
        self.public = True
        self.merge = False
        self.claimed = False
        self.living = False
        self.projects = []
        self.actions = []
        self.matches = {}
        self.guid = ""
        birth = "yyyy-mm-dd"
        death = "yyyy-mm-dd"
        if response:
            if "actions" in response:
                self.actions = response["actions"]
            if "guid" in response:
                self.guid = response["guid"]
            if "match_counts" in response:
                self.matches = response["match_counts"]
            if "master_profile" in response:
                self.master = response["master_profile"]
            if "public" in response:
                self.public = response["public"]
            if "merge_pending" in response:
                self.merge = response["merge_pending"]
            if "claimed" in response:
                self.claimed = response["claimed"]
            if "birth" in response:
                birth = response["birth"]
            if "death" in response:
                death = response["death"]
            if "living" in response:
                self.living = response["living"]
            else:
                self.message = "Access Denied"
            if "id" in response:
                self.id = response["id"]
            if "name" in response:
                self.name = response["name"]
            if "gender" in response:
                self.gender = response["gender"]
            else:
                self.gender = "Unknown"
            if "project_ids" in response:
                self.projects = [int(p.replace('project-', ' ')) for p in response["project_ids"]]

        self.group = ""
        self.blocation = "Unknown"
        self.dlocation = "Unknown"
        self.bcountry = None
        self.bstate = None
        self.dcountry = None
        self.dstate = None
        self.birth = "yyyy-mm-dd"
        self.birthcirca = ""
        self.death = "yyyy-mm-dd"
        self.deathcirca = ""
        self.process_lifespan(birth, death)

    def process_lifespan(self, birth, death):
        if birth:
            day = "dd"
            month = "mm"
            year = "yyyy"
            if "date" in birth:
                if "year" in birth["date"]:
                    year = str(birth["date"]["year"])
                if "month" in birth["date"]:
                    month = str(birth["date"]["month"]).zfill(2)
                if "day" in birth["date"]:
                    day = str(birth["date"]["day"]).zfill(2)
                if "before" in birth["date"]["formatted_date"]:
                    self.birthcirca = "bf."
                elif "after" in birth["date"]["formatted_date"]:
                    self.birthcirca = "af."
                elif "between" in birth["date"]["formatted_date"]:
                    self.birthcirca = "bt."
                if "circa" in birth["date"]["formatted_date"]:
                    self.birthcirca += "c."
                self.birth = year + "-" + month + "-" + day
            city = ""
            country = ""
            state = ""
            if "location" in birth:
                if "city" in birth["location"]:
                    city = birth["location"]["city"]
                    if "country" in birth["location"] or "state" in birth["location"]:
                        city += ", "
                if "state" in birth["location"]:
                    state = birth["location"]["state"]
                    self.bstate = state
                    self.bcountry = state  #Covers pre-US States that have no country listed
                    if "country" in birth["location"]:
                        state += ", "
                if "country" in birth["location"]:
                    country = birth["location"]["country"]
                    self.bcountry = country
                self.blocation = city + state + country
                if self.blocation.replace(",", "").strip() == "":
                    self.blocation = "Unknown"
                if self.blocation:
                    self.blocation = self.blocation.replace('"', "'")
                if self.bstate:
                    self.bstate = self.bstate.replace('"', "'")
                if self.bcountry:
                    self.bcountry = self.bcountry.replace('"', "'")

        if death:
            day = "dd"
            month = "mm"
            year = "yyyy"
            if "date" in death:
                if "year" in death["date"]:
                    year = str(death["date"]["year"])
                if "month" in death["date"]:
                    month = str(death["date"]["month"]).zfill(2)
                if "day" in death["date"]:
                    day = str(death["date"]["day"]).zfill(2)
                if "before" in death["date"]["formatted_date"]:
                    self.deathcirca = "bf."
                elif "after" in death["date"]["formatted_date"]:
                    self.deathcirca = "af."
                elif "between" in death["date"]["formatted_date"]:
                    self.deathcirca = "bt."
                if "circa" in death["date"]["formatted_date"]:
                    self.deathcirca += "c."
                self.death = year + "-" + month + "-" + day
            city = ""
            country = ""
            state = ""
            if "location" in death:
                if "city" in death["location"]:
                    city = death["location"]["city"]
                    if "country" in death["location"] or "state" in death["location"]:
                        city += ", "
                if "state" in death["location"]:
                    state = death["location"]["state"]
                    self.dstate = state
                    self.dcountry = state  #Covers pre-US States that have no country listed
                    if "country" in death["location"]:
                        state += ", "
                if "country" in death["location"]:
                    country = death["location"]["country"]
                    self.dcountry = country
                self.dlocation = city + state + country
                if self.dlocation.replace(",", "").strip() == "":
                    self.dlocation = "Unknown"
                if self.dlocation:
                    self.dlocation = self.dlocation.replace('"', "'")
                if self.dstate:
                    self.dstate = self.dstate.replace('"', "'")
                if self.dcountry:
                    self.dcountry = self.dcountry.replace('"', "'")

    def get_birth_location(self):
        return self.blocation

    def get_birth_country(self):
        return self.bcountry

    def get_birth_state(self):
        return self.bstate

    def get_birth_date(self):
        return self.birth

    def get_birth_circa(self):
        return self.birthcirca

    def get_death_location(self):
        return self.dlocation

    def get_death_country(self):
        return self.dcountry

    def get_death_state(self):
        return self.dstate

    def get_death_date(self):
        return self.death

    def get_death_circa(self):
        return self.deathcirca

    def get_id(self):
        return self.id

    def get_name(self):
        return self.name

    def get_gender(self):
        return self.gender

    def is_claimed(self):
        return self.claimed

    def is_master(self):
        return self.master

    def is_public(self):
        return self.public

    def is_living(self):
        return self.living

    def is_adopted(self):
        return self.adopted

    def merge_pending(self):
        return self.merge

    def set_group(self, group):
        self.group = group

    def get_group(self):
        return self.group

    def get_projects(self):
        return self.projects

    def set_message(self, message):
        self.message = message

    def get_message(self):
        return self.message

    def get_union(self):
        return self.union

    def get_adopted(self):
        return self.adopted

    def get_status(self):
        return self.status

    def get_actions(self):
        return self.actions

    def get_matches(self):
        return self.matches

    def get_guid(self):
        return self.guid

    def get_info(self):
        return {"name": self.get_name(), "id": self.get_id(), "relation": self.get_rel(), "union": self.get_union()}

    def get_date(self, event):
        eventstr = ""
        if event in self.response and "date" in self.response[event]:
            startstr = []
            evttime = self.response[event]["date"]
            if "circa" in evttime:
                startstr.append("Circa")
            if "month" in evttime:
                dt = date(2016, int(evttime["month"]), 1)
                startstr.append(dt.strftime("%b"))
            if "day" in evttime:
                startstr.append(str(evttime["day"]))
            if "year" in evttime:
                startstr.append(str(evttime["year"]))
            eventstr = " ".join(startstr)
            if "range" in evttime:
                eventstr = evttime["range"].title() + " " + eventstr
                if evttime["range"] == "between":
                    endstr = []
                    if "end_circa" in evttime:
                        endstr.append("Circa")
                    if "end_month" in evttime:
                        dt = date(2016, int(evttime["end_month"]), 1)
                        endstr.append(dt.strftime("%b"))
                    if "end_day" in evttime:
                        endstr.append(str(evttime["end_day"]))
                    if "end_year" in evttime:
                        endstr.append(str(evttime["end_year"]))
                    eventstr = eventstr + " and " + " ".join(endstr)
        return eventstr.strip()

    def get_location(self, event):
        eventstr = ""
        if event in self.response:
            evttime = self.response[event]
            location = []
            if "location" in evttime:
                if "place_name" in evttime["location"]:
                    location.append(evttime["location"]["place_name"])
                if "city" in evttime["location"]:
                    location.append(evttime["location"]["city"])
                if "county" in evttime["location"]:
                    location.append(evttime["location"]["county"])
                if "state" in evttime["location"]:
                    location.append(evttime["location"]["state"])
                if "country" in evttime["location"]:
                    location.append(evttime["location"]["country"])
                eventstr = ", ".join(location)
        return eventstr

    def get_full_info(self, adopt=None):
        birth = self.get_date("birth")
        death = self.get_date("death")
        baptism = self.get_date("baptism")
        burial = self.get_date("burial")
        birthloc = self.get_location("birth")
        deathloc = self.get_location("death")
        baptismloc = self.get_location("baptism")
        burialloc = self.get_location("burial")
        marriage = self.get_date("marriage")
        marriageloc = self.get_location("marriage")
        divorce = self.get_date("divorce")
        divorceloc = self.get_location("divorce")
        if birth != "":
            self.response["birth"]["date"] = birth
        if birthloc != "":
            self.response["birth"]["location_string"] = birthloc
        if baptism != "":
            self.response["baptism"]["date"] = baptism
        if baptismloc != "":
            self.response["baptism"]["location_string"] = baptismloc
        if death != "":
            self.response["death"]["date"] = death
        if deathloc != "":
            self.response["death"]["location_string"] = deathloc
        if burial != "":
            self.response["burial"]["date"] = burial
        if burialloc != "":
            self.response["burial"]["location_string"] = burialloc
        if marriage != "":
            self.response["marriage"]["date"] = marriage
        if marriageloc != "":
            self.response["marriage"]["location_string"] = marriageloc
        if divorce != "":
            self.response["divorce"]["date"] = divorce
        if divorce != "":
            self.response["divorce"]["location_string"] = divorceloc
        self.response["relation"] = self.relation
        self.response["union"] = self.get_union()
        if adopt:
            self.response["adopted"] = self.get_adopted()
        self.response["status"] = self.get_status()
        self.response["actions"] = self.get_actions()
        self.response["matches"] = self.get_matches()
        self.response["guid"] = self.get_guid()
        return self.response

    def get_rel(self, gen=0):
        if gen == 0:
            return self.relation
        elif gen == -1:
            return "Selected Person"
        else:
            #todo likely needs some work on half siblings, step parents, gen 1, etc.
            newrel = self.relation
            if self.relation == "sister":
                newrel = "aunt"
            elif self.relation == "brother":
                newrel = "uncle"
            elif self.relation == "sibling":
                newrel = "aunt/uncle"
            elif self.relation == "father":
                newrel = "grandfather"
            elif self.relation == "mother":
                newrel = "grandmother"
            elif self.relation == "wife":
                newrel = "spouse"
            elif self.relation == "husband":
                newrel = "spouse"
            elif self.relation == "spouse":
                newrel = "spouse"
            elif self.relation == "partner":
                newrel = "partner"
            else:
                newrel = "aunt/uncle/grandparent"
        prefix = ""
        gen -= 1
        if gen > 0:
            prefix = "great "
        if gen > 1:
            if gen == 2:
                prefix = "2nd " + prefix
            elif gen == 3:
                prefix = "3rd " + prefix
            elif gen > 3:
                if gen < 21:
                    prefix = str(gen) + "th " + prefix
                elif gen % 10 == 1:
                    prefix = str(gen) + "st " + prefix
                elif gen % 10 == 2:
                    prefix = str(gen) + "nd " + prefix
                elif gen % 10 == 3:
                    prefix = str(gen) + "rd " + prefix
                else:
                    prefix = str(gen) + "th " + prefix
        return prefix + newrel


class Union(object):
    def __init__(self, id, response):
        self.id = id
        self.edges = []
        self.status = ""
        self.marriage = None
        self.divorce = None
        if "status" in response:
            self.status = response["status"]
        if "edges" in response:
            for item in response["edges"]:
                adopt = False
                if "rel_modifier" in response["edges"][item]:
                    adopt = True
                edge = Edge(item, response["edges"][item]["rel"], self.id, adopt)
                if edge:
                    self.edges.append(edge)
        if "marriage" in response:
            self.marriage = response["marriage"]
        if "divorce" in response:
            self.divorce = response["divorce"]

    def print_union(self):
        logging.info(self.id + " (" + self.status + ")")
        for edge in self.edges:
            logging.info("\t" + edge.profile + " (" + edge.rel + ")")

    def get_type(self, rel):
        for x in self.edges:
            rel2 = x.get_rel()
            if rel == "partner" and rel2 == "child":
                return "parent"
            elif rel == "partner" and rel2 == "partner" and self.status == "spouse":
                return "spouse"
            elif rel == "partner" and rel2 == "partner" and self.status == "partner":
                return "partner"
            elif rel == "child" and rel2 == "partner":
                return "child"
            elif rel == "child" and rel2 == "child":
                return "sibling"
            else:
                return "unknown"

    def details(self, response):
        if self.marriage:
            response["marriage"] = self.marriage
        if self.divorce:
            response["divorce"] = self.divorce
        return response

    def get_edge(self, profile, focus, rel, gender, name, response):
        for x in self.edges:
            if focus == x.get_profile():
                rel2 = x.get_rel()
                if profile == focus:
                    return Relative(profile, name, "focus", response, self.id, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "child" and gender == "male":
                    return Relative(profile, name, "father", self.details(response), self.id, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "child" and gender == "female":
                    return Relative(profile, name, "mother", self.details(response), self.id, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "child":
                    return Relative(profile, name, "parent", self.details(response), self.id, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "partner" and gender == "male" and (self.status == "spouse" or self.status == "ex_spouse"):
                    return Relative(profile, name, "husband", self.details(response), self.id, status=self.status, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "partner" and gender == "female" and (self.status == "spouse" or self.status == "ex_spouse"):
                    return Relative(profile, name, "wife", self.details(response), self.id, status=self.status, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "partner" and (self.status == "spouse" or self.status == "ex_spouse"):
                    return Relative(profile, name, "spouse", self.details(response), self.id, status=self.status, adopt=x.is_adopted())
                elif rel == "partner" and rel2 == "partner" and self.status == "partner":
                    return Relative(profile, name, "partner", response, self.id, status=self.status, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "partner" and gender == "male":
                    return Relative(profile, name, "son", response, self.id, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "partner" and gender == "female":
                    return Relative(profile, name, "daughter", response, self.id, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "partner":
                    return Relative(profile, name, "child", response, self.id, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "child" and gender == "male":
                    return Relative(profile, name, "brother", response, self.id, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "child" and gender == "female":
                    return Relative(profile, name, "sister", response, self.id, adopt=x.is_adopted())
                elif rel == "child" and rel2 == "child":
                    return Relative(profile, name, "sibling", response, self.id, adopt=x.is_adopted())
                else:
                    return None

    def get_id(self):
        return self.id


class Edge(object):
    def __init__(self, profile, rel, union, adopt=False):
        self.profile = profile
        self.rel = rel
        self.union = union
        self.adopt = adopt

    def get_profile(self):
        return self.profile

    def get_rel(self):
        return self.rel

    def get_union(self):
        return self.union

    def is_adopted(self):
        return self.adopt


class GeniAPIError(Exception):
    def __init__(self, result):
        #Exception.__init__(self, message)
        #self.type = type
        self.result = result
        try:
            self.type = result["error_code"]
        except:
            self.type = ""

        # OAuth 2.0 Draft 10
        try:
            self.message = result["error_description"]
        except:
            # OAuth 2.0 Draft 00
            try:
                self.message = result["error"]["message"]
            except:
                # REST server style
                try:
                    self.message = result["error_msg"]
                except:
                    self.message = result

        Exception.__init__(self, self.message)

